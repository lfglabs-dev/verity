import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativePrimOps
import Lean

namespace Compiler.Proofs.YulGeneration.Backends.Native

open Compiler.Yul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends.StateBridge
open Lean Elab Tactic Meta
open Compiler.Proofs.IRGeneration
  (IRResult IRState IRStorageSlot IRStorageWord IRTransaction)

/-- Lean 4.31 exposes optional byte-array access through its backing array. -/
def byteArrayGet? (a : ByteArray) (i : Nat) : Option UInt8 :=
  a.data[i]?

/-- Native evaluation of the lowered generated selector expression peels to
    exactly EVMYulLean `calldataload(0)` followed by `shr(224, ...)`. -/
theorem eval_lowerExprNative_selectorExpr_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.shiftRight
          (EvmYul.State.calldataload shared.toState (EvmYul.UInt256.ofNat 0))
          (EvmYul.UInt256.ofNat Compiler.Constants.selectorShift)) := by
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', Compiler.Constants.selectorShift]

theorem eval_lowerExprNative_selectorExpr_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus)) := by
  rw [eval_lowerExprNative_selectorExpr_ok]
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  rw [hv]

/-- Native evaluation of the lowered `iszero(lt(calldatasize(), 4))` Yul
    expression — the `__has_selector` initializer that `buildSwitch` emits —
    reduces to the concrete `UInt256` predicate `isZero(lt(ofNat cd_size, 4))`,
    where `cd_size` is the calldata byte size in the current execution
    environment. This is the eval-side primitive needed to chain
    `let __has_selector := …` through `exec_let_prim_one_ok` in the
    selector-miss/hit dispatcher proof. -/
theorem eval_lowerExprNative_iszero_lt_calldatasize_4_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero"
            [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]]))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_iszero,
    Backends.lookupRuntimePrimOp_lt, Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- For any natural `n` representable as a `UInt256` and at least `4`, the
    EVMYulLean primitive `LT(ofNat n, 4)` evaluates to the canonical zero word.
    This is the closed-form predicate fact needed to specialise
    `eval_lowerExprNative_iszero_lt_calldatasize_4_ok` to the dispatcher's
    initial state, where calldata size is `4 + tx.args.length * 32`. -/
private theorem uint256_lt_ofNat_4_eq_zero_of_ge
    (n : Nat) (hLe : 4 ≤ n) (hSize : n < EvmYul.UInt256.size) :
    EvmYul.UInt256.lt (EvmYul.UInt256.ofNat n) (EvmYul.UInt256.ofNat 4) =
      EvmYul.UInt256.ofNat 0 := by
  have hN : (EvmYul.UInt256.ofNat n).val.val = n := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hSize]
  have h4 : (EvmYul.UInt256.ofNat 4).val.val = 4 := by
    unfold EvmYul.UInt256.ofNat
    decide
  have hNotLt : ¬ ((EvmYul.UInt256.ofNat n : EvmYul.UInt256) <
      (EvmYul.UInt256.ofNat 4 : EvmYul.UInt256)) := by
    intro hLt
    have hh : (EvmYul.UInt256.ofNat n).val.val <
        (EvmYul.UInt256.ofNat 4).val.val := hLt
    rw [hN, h4] at hh
    omega
  simp [EvmYul.UInt256.lt, hNotLt]

/-- The canonical zero `UInt256` is its own `isZero`-predecessor in the sense
    that `ISZERO 0 = 1`. -/
private theorem uint256_isZero_ofNat_zero :
    EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 0) = EvmYul.UInt256.ofNat 1 := by
  decide

/-- Specialisation of
    `eval_lowerExprNative_iszero_lt_calldatasize_4_ok` to the dispatcher's
    initial bridged state. Because `calldata.size = 4 + tx.args.length * 32`
    and the no-wrap hypothesis keeps that within the `UInt256` range, the
    `__has_selector` initializer reduces to the concrete value `1`. This is
    the eval-side primitive that lets the selector-hit path of the dispatcher
    fire (and the selector-miss path is then ruled out by `iszero(1) = 0`). -/
theorem eval_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.eval 10
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero"
            [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit 4]]))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        EvmYul.UInt256.ofNat 1) := by
  rw [eval_lowerExprNative_iszero_lt_calldatasize_4_ok,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- Native evaluation of the lowered `callvalue()` Yul expression.
    The EVMYulLean primitive `CALLVALUE` is a zero-argument execution-env op
    that returns the current execution environment's `weiValue`. Closes the
    eval-side seam for callvalue-guard reasoning on dispatcher inner blocks. -/
theorem eval_lowerExprNative_callvalue_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval 5
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store, shared.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp_callvalue,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- Specialisation of `eval_lowerExprNative_callvalue_ok` to the dispatcher's
    initial bridged state: the result is the literal `natToUInt256 tx.msgValue`
    via `initialState_weiValue`. -/
theorem eval_lowerExprNative_callvalue_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.eval 5
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok (.Ok (initialState contract tx storage observableSlots).sharedState ∅,
        natToUInt256 tx.msgValue) := by
  rw [eval_lowerExprNative_callvalue_ok, initialState_weiValue]

/-- Fuel-parametric form of `eval_lowerExprNative_callvalue_ok`. -/
theorem eval_lowerExprNative_callvalue_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval (fuel + 5)
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store, shared.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp_callvalue,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- Native evaluation of the lowered `lt(calldatasize(), k)` Yul expression
    (the inner argument-length revert guard `if lt(calldatasize(), K) {…}` that
    `dispatchBody` emits before each function-arg-length-checked body). At any
    fuel `≥ fuel + 7`, the eval reduces to the concrete `UInt256` predicate
    `LT(ofNat cd_size, ofNat k)`, where `cd_size` is the calldata byte size in
    the current execution environment. Closes the eval-side seam for
    lt-calldatasize-guard reasoning on dispatcher hit-case body inner blocks. -/
theorem eval_lowerExprNative_lt_calldatasize_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (k : Nat) :
    EvmYul.Yul.eval (fuel + 8)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit k]))
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store,
        EvmYul.UInt256.lt
          (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
          (EvmYul.UInt256.ofNat k)) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_lt,
    Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.executionEnv]

/-- State-generic native evaluation of the lowered `lt(calldatasize(), k)`
expression. At any fuel ≥ 8, eval returns the SAME state unchanged with value
`lt(s.executionEnv.calldata.size, k)`. Works for any state form (Ok,
OutOfFuel, Checkpoint) because the underlying `executionEnvOp` and
`dispatchBinary` are state-preserving (no shape-match on state). -/
theorem eval_lowerExprNative_lt_calldatasize_fuel
    (fuel : Nat)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (k : Nat) :
    EvmYul.Yul.eval (fuel + 8)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit k]))
        codeOverride s =
      .ok (s,
        EvmYul.UInt256.lt
          (EvmYul.UInt256.ofNat s.executionEnv.calldata.size)
          (EvmYul.UInt256.ofNat k)) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_lt,
    Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head']

/-- Tight (minimum-fuel) state-generic version: eval succeeds at fuel ≥ 6. -/
theorem eval_lowerExprNative_lt_calldatasize_fuel_ge_6
    (fuel : Nat)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (k : Nat) :
    EvmYul.Yul.eval (fuel + 6)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit k]))
        codeOverride s =
      .ok (s,
        EvmYul.UInt256.lt
          (EvmYul.UInt256.ofNat s.executionEnv.calldata.size)
          (EvmYul.UInt256.ofNat k)) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_lt,
    Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head']

/-- State-generic native evaluation of the lowered `callvalue()` expression.
At any fuel ≥ 5, eval returns the SAME state unchanged with value
`s.executionEnv.weiValue`. Works for any state form. -/
theorem eval_lowerExprNative_callvalue_fuel
    (fuel : Nat)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval (fuel + 5)
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride s =
      .ok (s, s.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp_callvalue,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head']

/-- Tight (minimum-fuel) state-generic version: eval succeeds at fuel ≥ 2. -/
theorem eval_lowerExprNative_callvalue_fuel_ge_2
    (fuel : Nat)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    EvmYul.Yul.eval (fuel + 2)
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride s =
      .ok (s, s.executionEnv.weiValue) := by
  simp [Backends.lookupRuntimePrimOp_callvalue,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.head']

/-- At fuel `n + 8` with Ok input state, the dispatcher's `lt(calldatasize, k)`
guard eval returns the same Ok state, so `final.reviveJump = state.reviveJump`.
Direct corollary of `eval_lowerExprNative_lt_calldatasize_ok_fuel`. -/
theorem eval_lt_calldatasize_lit_preserves_reviveJump_of_ok_at_fuel
    (k : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (n : Nat) :
    ∀ final v,
      EvmYul.Yul.eval (n + 8)
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit k]))
          codeOverride (.Ok shared store) = .ok (final, v) →
        final.reviveJump = (EvmYul.Yul.State.Ok shared store).reviveJump := by
  intro final v hEval
  rw [eval_lowerExprNative_lt_calldatasize_ok_fuel] at hEval
  obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
  rw [hStateEq]

/-- At fuel `n + 5` with Ok input state, the dispatcher's `callvalue()` guard
eval returns the same Ok state, so `final.reviveJump = state.reviveJump`.
Direct corollary of `eval_lowerExprNative_callvalue_ok_fuel`. Used to discharge
the `hCallvalueReviveJump` premise of
`NativeBlockPreservesWord_revived_switchCaseBody_nonpayable_of_user_body` when
the caller can establish Ok input form (the dispatcher's actual case at the
selected-body entry). -/
theorem eval_callvalue_preserves_reviveJump_of_ok_at_fuel
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (n : Nat) :
    ∀ final v,
      EvmYul.Yul.eval (n + 5)
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          codeOverride (.Ok shared store) = .ok (final, v) →
        final.reviveJump = (EvmYul.Yul.State.Ok shared store).reviveJump := by
  intro final v hEval
  rw [eval_lowerExprNative_callvalue_ok_fuel] at hEval
  obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
  rw [hStateEq]

/-- State-generic reviveJump preservation for `lt(calldatasize, k)` at
fuel ≥ 8. -/
theorem eval_lt_calldatasize_lit_preserves_reviveJump_at_fuel_ge_8
    (k : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State)
    (n : Nat) :
    ∀ final v,
      EvmYul.Yul.eval (n + 8)
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit k]))
          codeOverride s = .ok (final, v) →
        final.reviveJump = s.reviveJump := by
  intro final v hEval
  rw [eval_lowerExprNative_lt_calldatasize_fuel] at hEval
  obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
  rw [hStateEq]

/-- State-generic reviveJump preservation for `callvalue()` at fuel ≥ 5. -/
theorem eval_callvalue_preserves_reviveJump_at_fuel_ge_5
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (s : EvmYul.Yul.State)
    (n : Nat) :
    ∀ final v,
      EvmYul.Yul.eval (n + 5)
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          codeOverride s = .ok (final, v) →
        final.reviveJump = s.reviveJump := by
  intro final v hEval
  rw [eval_lowerExprNative_callvalue_fuel] at hEval
  obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
  rw [hStateEq]

/-- For fuel < 2, eval of the lowered `callvalue()` expression errors out:
the outer `.Call` decrement plus inner `evalArgs 0` returns `.error
.OutOfFuel`. -/
private theorem eval_lowerExprNative_callvalue_lt2_not_ok
    (fuel : Nat) (hLT : fuel < 2)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (result : EvmYul.Yul.State × EvmYul.Literal) :
    EvmYul.Yul.eval fuel
        (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
        codeOverride s ≠ .ok result := by
  intro hEval
  rcases fuel with _ | _ | _
  all_goals first
    | omega
    | (simp [Backends.lookupRuntimePrimOp_callvalue,
        EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalPrimCall,
        EvmYul.Yul.reverse'] at hEval)

/-- UNIVERSAL-INPUT reviveJump discharge for the dispatcher's `callvalue()`
guard: for ANY fuel and ANY state, a successful eval preserves `reviveJump`.
This is the closed lemma that callers of
`NativeStmtPreservesWord_revived_if_of_cond_preserves_reviveJump` apply
blind for the callvalue guard. -/
theorem eval_callvalue_preserves_reviveJump
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    ∀ fuel state final v,
      EvmYul.Yul.eval fuel
          (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" []))
          codeOverride state = .ok (final, v) →
        final.reviveJump = state.reviveJump := by
  intro fuel state final v hEval
  by_cases hFuel : fuel ≥ 2
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
    rw [eval_lowerExprNative_callvalue_fuel_ge_2] at hEval
    obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
    rw [hStateEq]
  · exact absurd hEval
      (eval_lowerExprNative_callvalue_lt2_not_ok fuel (by omega)
        state codeOverride (final, v))

set_option maxHeartbeats 4000000 in
/-- For fuel < 6, eval of the lowered `lt(calldatasize, k)` expression errors
out: the deeply nested Call/PrimCall structure consumes 6 fuel units before
the inner CALLDATASIZE primop's `executionEnvOp` runs. -/
private theorem eval_lowerExprNative_lt_calldatasize_lt6_not_ok
    (fuel : Nat) (hLT : fuel < 6)
    (s : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (k : Nat) (result : EvmYul.Yul.State × EvmYul.Literal) :
    EvmYul.Yul.eval fuel
        (Backends.lowerExprNative
          (Yul.YulExpr.call "lt"
            [Yul.YulExpr.call "calldatasize" [],
             Yul.YulExpr.lit k]))
        codeOverride s ≠ .ok result := by
  intro hEval
  rcases fuel with _ | _ | _ | _ | _ | _ | _
  all_goals first
    | omega
    | (simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_lt,
        Backends.lookupRuntimePrimOp_calldatasize,
        EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
        EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons'] at hEval)

/-- UNIVERSAL-INPUT reviveJump discharge for the dispatcher's
`lt(calldatasize, k)` guard: for ANY fuel and ANY state, a successful eval
preserves `reviveJump`. Closes the `hCondReviveJump` premise for this
guard. -/
theorem eval_lt_calldatasize_lit_preserves_reviveJump
    (k : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    ∀ fuel state final v,
      EvmYul.Yul.eval fuel
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit k]))
          codeOverride state = .ok (final, v) →
        final.reviveJump = state.reviveJump := by
  intro fuel state final v hEval
  by_cases hFuel : fuel ≥ 6
  · obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 6 := ⟨fuel - 6, by omega⟩
    rw [eval_lowerExprNative_lt_calldatasize_fuel_ge_6] at hEval
    obtain ⟨hStateEq, _⟩ := Prod.mk.inj (Except.ok.inj hEval)
    rw [hStateEq]
  · exact absurd hEval
      (eval_lowerExprNative_lt_calldatasize_lt6_not_ok fuel (by omega)
        state codeOverride k (final, v))

/-- Native evaluation of the lowered `sload(lit slot)` Yul expression. At any
    fuel `≥ fuel + 6`, the eval reduces to the closed-form pair returned by
    EVMYulLean's `SLOAD` primitive: the new `SharedState` carries the
    storage-access-tracked `toState`, and the value is the raw
    `State.sload` result word. Closes the eval-side seam for sload reasoning
    on dispatcher hit-case body inner blocks (specifically the
    `mstore(0, sload(0))` outer expression in the `retrieve()` getter
    body). -/
theorem eval_lowerExprNative_sload_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (slot : Nat) :
    EvmYul.Yul.eval (fuel + 6)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]))
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat slot)
      .ok (.Ok { shared with toState := state' } store, value) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_sload,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head', EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState]

/-- State-generic native `exec` of the `mstore(memOffset, sload(slot))`
    expression statement that the generated `retrieve()` body uses to
    materialise the slot-zero word into memory before `return(0,32)`.
    The exec threads the closed-form sload→mstore state effect: storage
    is read with access-tracking via `SharedState.sload`, and memory is
    updated with `MachineState.mstore` of the resulting value at the
    given offset. The Yul `VarStore` is unchanged. -/
theorem exec_lowerExprNative_mstore_lit_sload_lit_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset slot : Nat) :
    EvmYul.Yul.exec (fuel + 8)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit memOffset,
             Yul.YulExpr.call "sload" [Yul.YulExpr.lit slot]])))
        codeOverride (.Ok shared store) =
      let (state', value) := shared.sload (EvmYul.UInt256.ofNat slot)
      let shared' : EvmYul.SharedState .Yul := { shared with toState := state' }
      .ok (.Ok { shared' with
                 toMachineState :=
                   shared'.toMachineState.mstore
                     (EvmYul.UInt256.ofNat memOffset) value }
            store) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_mstore,
    Backends.lookupRuntimePrimOp_sload,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.toState,
    EvmYul.Yul.State.toSharedState, EvmYul.Yul.State.setSharedState,
    EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.toMachineState]

/-- State-generic native `exec` of `mstore(memOffset, value)` when both
    operands are generated literals. The Yul `VarStore` is unchanged and only
    the machine memory is updated. -/
theorem exec_lowerExprNative_mstore_lit_lit_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset value : Nat) :
    EvmYul.Yul.exec (fuel + 6)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit memOffset, Yul.YulExpr.lit value])))
        codeOverride (.Ok shared store) =
      .ok (.Ok { shared with
                 toMachineState :=
                   shared.toMachineState.mstore
                     (EvmYul.UInt256.ofNat memOffset)
                     (EvmYul.UInt256.ofNat value) }
            store) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_mstore,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.toMachineState]

/-- State-generic native `exec` of `mstore(memOffset, calldataload(cdOffset))`.
    The calldata read does not mutate shared state; only machine memory is
    updated with the loaded word. -/
theorem exec_lowerExprNative_mstore_lit_calldataload_lit_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset cdOffset : Nat) :
    EvmYul.Yul.exec (fuel + 8)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit memOffset,
             Yul.YulExpr.call "calldataload" [Yul.YulExpr.lit cdOffset]])))
        codeOverride (.Ok shared store) =
      .ok (.Ok { shared with
                 toMachineState :=
                   shared.toMachineState.mstore
                     (EvmYul.UInt256.ofNat memOffset)
                     (shared.calldataload (EvmYul.UInt256.ofNat cdOffset)) }
            store) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_mstore,
    Backends.lookupRuntimePrimOp_calldataload,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.toMachineState,
    EvmYul.Yul.State.setMachineState]

/-- State-generic native `exec` of the `return(memOffset, memSize)` expression
    statement that the generated `retrieve()` body uses to surface the
    materialised slot-zero word as the call's return data. EVMYulLean models
    `RETURN` as a Yul halt carrying the post-`evmReturn` machine state; the
    halt literal is the canonical nonzero marker `⟨1⟩` produced by
    `binaryMachineStateOp`, while the actual returned bytes live in the
    state's `H_return` buffer. The Yul `VarStore` is unchanged. -/
theorem exec_lowerExprNative_return_lit_lit_error_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset memSize : Nat) :
    EvmYul.Yul.exec (fuel + 6)
        (.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit memOffset, Yul.YulExpr.lit memSize])))
        codeOverride (.Ok shared store) =
      .error (EvmYul.Yul.Exception.YulHalt
        (.Ok { shared with
               toMachineState :=
                 shared.toMachineState.evmReturn
                   (EvmYul.UInt256.ofNat memOffset)
                   (EvmYul.UInt256.ofNat memSize) }
          store)
        ⟨1⟩) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_return,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.binaryMachineStateOp, EvmYul.Yul.State.setMachineState,
    EvmYul.Yul.State.toMachineState, EvmYul.Yul.multifill']

/-- Singleton-block form of `exec_lowerExprNative_return_lit_lit_error_fuel`.
    A block whose only statement is `return(memOffset, memSize)` exec-errors
    with the same closed-form `YulHalt` as the bare statement, plus one
    extra unit of fuel for the `Block` cons step. This lets compositional
    proofs that need to peel an outer block via `exec_block_cons_tail_error`
    discharge the singleton-tail obligation directly. -/
theorem exec_block_singleton_lowerExprNative_return_lit_lit_error_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (memOffset memSize : Nat) :
    EvmYul.Yul.exec (fuel + 7)
        (.Block [.ExprStmtCall (Backends.lowerExprNative
          (Yul.YulExpr.call "return"
            [Yul.YulExpr.lit memOffset, Yul.YulExpr.lit memSize]))])
        codeOverride (.Ok shared store) =
      .error (EvmYul.Yul.Exception.YulHalt
        (.Ok { shared with
               toMachineState :=
                 shared.toMachineState.evmReturn
                   (EvmYul.UInt256.ofNat memOffset)
                   (EvmYul.UInt256.ofNat memSize) }
          store)
        ⟨1⟩) := by
  show EvmYul.Yul.exec (Nat.succ (fuel + 6)) _ codeOverride _ = _
  have hHead := exec_lowerExprNative_return_lit_lit_error_fuel
    fuel shared store codeOverride memOffset memSize
  simp [EvmYul.Yul.exec, hHead]

/-- State-generic native `exec` of the `let __has_selector := iszero(lt(
    calldatasize(), 4))` statement that `buildSwitch` emits at the head of a
    dispatcher inner-block: at any fuel `≥ 11`, the let assigns
    `name ↦ isZero(lt(ofNat cd_size, 4))` to the variable store, where
    `cd_size = shared.executionEnv.calldata.size`. The closed-form numeric
    evaluation of `isZero(lt(_, _))` is then performed by the initial-state
    specialization below. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier) :
    EvmYul.Yul.exec 11
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        codeOverride (.Ok shared store) =
      .ok ((.Ok shared store : EvmYul.Yul.State).insert name
        (EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4)))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_iszero,
    Backends.lookupRuntimePrimOp_lt, Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.executionEnv]

/-- Specialisation of `exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok`
    to the dispatcher's initial bridged state. With the no-wrap hypothesis on
    `4 + tx.args.length * 32`, the `__has_selector` variable receives the
    closed-form word `UInt256.ofNat 1`. This is the exec-side primitive the
    dispatcher proof needs immediately after the dispatcher inner-block is
    pinned to its `let / if / if` shape: it lets the selector-miss `If` guard
    fail and the selector-hit `If` guard fire. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (name : EvmYul.Identifier)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec 11
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
            EvmYul.Yul.State).insert name (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- Fuel-parametric form of
    `exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok`. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok_fuel
    (fuel : Nat)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        codeOverride (.Ok shared store) =
      .ok ((.Ok shared store : EvmYul.Yul.State).insert name
        (EvmYul.UInt256.isZero
          (EvmYul.UInt256.lt
            (EvmYul.UInt256.ofNat shared.executionEnv.calldata.size)
            (EvmYul.UInt256.ofNat 4)))) := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_iszero,
    Backends.lookupRuntimePrimOp_lt, Backends.lookupRuntimePrimOp_calldatasize,
    EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    EvmYul.Yul.State.executionEnv]

/-- Fuel-parametric form of
    `exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok`. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (name : EvmYul.Identifier)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
            EvmYul.Yul.State).insert name (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok_fuel,
      initialState_calldataSize,
      uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
      uint256_isZero_ofNat_zero]

/-- The native lowering shape of the selector-miss guard.  Keep this
explicit: Lean 4.31 does not unfold this lowering definitionally through the
`change` tactic. -/
private theorem lowerExprNative_iszero_ident_shape
    (name : EvmYul.Identifier) :
    Backends.lowerExprNative
        (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident (name : String)]) =
      .Call (.inl .ISZERO) [.Var (name : String)] := by
  simp [Backends.lowerExprNative, Backends.lookupRuntimePrimOp_iszero]

/-- State-generic native `eval` of the lowered selector-miss guard
    `iszero(__has_selector)`: when the named variable is bound to
    `UInt256.ofNat 1` in the variable store, the guard evaluates to
    the canonical zero `UInt256` literal. This is the eval primitive that
    feeds `exec_if_eval_zero` to skip the selector-miss `revert(0,0)` body. -/
theorem eval_lowerExprNative_iszero_ident_one_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 8
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident (name : String)]))
        codeOverride state =
      .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [lowerExprNative_iszero_ident_shape]
  simp [EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head']
  calc
    EvmYul.UInt256.isZero state[name]! =
        EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 1) := congrArg _ hVal
    _ = EvmYul.UInt256.ofNat 0 := by decide

/-- Fuel-parametric form of `eval_lowerExprNative_iszero_ident_one_ok`. -/
theorem eval_lowerExprNative_iszero_ident_one_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 8)
        (Backends.lowerExprNative
          (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident (name : String)]))
        codeOverride state =
      .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [lowerExprNative_iszero_ident_shape]
  simp [EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse', EvmYul.Yul.cons',
    EvmYul.Yul.head']
  calc
    EvmYul.UInt256.isZero state[name]! =
        EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 1) := congrArg _ hVal
    _ = EvmYul.UInt256.ofNat 0 := by decide

theorem exec_let_lowerExprNative_selectorExpr_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec 11
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

theorem exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract) (.Ok (initialState contract tx storage observableSlots).sharedState ∅) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState ∅ :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

/-- Store-parametric form of `exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel`.
    The lowered selector eval reads only calldata from the shared state, so
    the `let __discr := selectorExpr` step is invariant under any preceding
    native-side varstore. Lets us chain the dispatcher prefix's discriminator
    binding on a state that already carries `__has_selector := 1` (left by
    the buildSwitch wrapper). -/
theorem exec_let_lowerExprNative_selectorExpr_initialState_store_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract)
        (.Ok (initialState contract tx storage observableSlots).sharedState store) =
      .ok ((.Ok (initialState contract tx storage observableSlots).sharedState store :
          EvmYul.Yul.State).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (initialState contract tx storage observableSlots).sharedState)
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [Compiler.Constants.selectorShift] using hv
  rw [lowerExprNative_selectorExpr]
  simp [EvmYul.Yul.exec, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall,
    EvmYul.Yul.reverse', EvmYul.Yul.cons', EvmYul.Yul.head',
    EvmYul.Yul.multifill', EvmYul.Yul.State.multifill,
    Compiler.Constants.selectorShift]
  rw [hv224]

@[simp] theorem exec_let_lit_ok
    (fuel' : Nat)
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel')
        (.Let [name] (some (.Lit value))) codeOverride state =
      .ok (state.insert name value) := by
  simp [EvmYul.Yul.exec]

/-- If the head statement of a native block finishes normally, execution
    continues with the remaining block statements at the same decremented fuel. -/
theorem exec_block_cons_ok
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next final : EvmYul.Yul.State)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next)
    (hTail : EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next = .ok final) :
  EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .ok final := by
  simp [EvmYul.Yul.exec, hHead, hTail]

/-- Tail-generic peel of a native block whose head statement finishes
    normally: the whole block exec at `succ fuel'` equals the residual block
    exec on the post-head state at the same fuel `fuel'`, regardless of how
    that residual exec finally evaluates. Useful when the rest of the proof
    stays open (e.g. when the next peel is a chained equation rather than a
    closed `.ok final`). -/
theorem exec_block_cons_ok_eq
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next := by
  simp [EvmYul.Yul.exec, hHead]

/-- If the head statement of a native block halts or errors, the whole block
    halts or errors immediately. -/
theorem exec_block_cons_error
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hHead]

/-- If the head statement of a native block finishes normally but the tail
    halts or errors, the whole block halts or errors after the head update. -/
theorem exec_block_cons_tail_error
    (fuel' : Nat)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (stmts : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hHead : EvmYul.Yul.exec fuel' stmt codeOverride state = .ok next)
    (hTail : EvmYul.Yul.exec fuel' (.Block stmts) codeOverride next = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block (stmt :: stmts)) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hHead, hTail]

/-- Execute an appended native block when the left block consumes exactly its
    statement-count fuel prefix and the right block runs at the remaining fuel.

This matches EVMYulLean's block interpreter: every cons step decrements the fuel
available to both the head statement and the tail block. -/
theorem exec_block_append_ok
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) (state middle final : EvmYul.Yul.State)
    (hLeft : EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state = .ok middle)
    (hRight : EvmYul.Yul.exec (fuel + k) (.Block right) codeOverride middle = .ok final) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right)) codeOverride state = .ok final := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft hRight ⊢
      cases remaining with
      | zero =>
          have hLeft0 : EvmYul.Yul.exec 0 (.Block []) codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeft0
      | succ remaining' =>
          have hLeftS : EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
              codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
          cases hLeftS
          simpa [hFuel] using hRight
  | cons stmt rest ih =>
      have hFuel : fuel + (stmt :: rest).length + k =
          fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' : EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
          (.Block (stmt :: rest)) codeOverride state = .ok middle := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead : EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state =
        head at hLeft'
      cases head with
      | error err => simp at hLeft'
      | ok next =>
          simp at hLeft'
          have hTail : EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
              codeOverride next = .ok middle := hLeft'
          have hRest : EvmYul.Yul.exec (fuel + rest.length + k)
              (.Block (rest ++ right)) codeOverride next = .ok final :=
            ih fuel next hTail hRight
          have hBlock := exec_block_cons_ok (fuel + rest.length + k)
            stmt (rest ++ right) codeOverride state next final hHead hRest
          have hGoalFuel : fuel + rest.length + k + 1 =
              fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hBlock

/-- Execute an appended native block when the left block finishes normally and
    the right block halts or errors at the remaining fuel. -/
theorem exec_block_append_error
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state middle : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hLeft :
      EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state =
        .ok middle)
    (hRight :
      EvmYul.Yul.exec (fuel + k) (.Block right) codeOverride middle =
        .error err) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right))
      codeOverride state = .error err := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft hRight ⊢
      cases remaining with
      | zero =>
          have hLeft0 :
              EvmYul.Yul.exec 0 (.Block []) codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeft0
      | succ remaining' =>
          have hLeftS :
              EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
                codeOverride state = .ok middle := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
          cases hLeftS
          simpa [hFuel] using hRight
  | cons stmt rest ih =>
      have hFuel :
          fuel + (stmt :: rest).length + k = fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' :
          EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
            (.Block (stmt :: rest)) codeOverride state = .ok middle := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead :
        EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state = head
        at hLeft'
      cases head with
      | error err' =>
          simp at hLeft'
      | ok next =>
          simp at hLeft'
          have hTail :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
                codeOverride next = .ok middle := hLeft'
          have hRest :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block (rest ++ right))
                codeOverride next = .error err :=
            ih fuel next hTail hRight
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_tail_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state next err hHead hRest)

/-- If an appended block's left prefix halts or errors, the full appended block
    halts or errors before reaching the right suffix. -/
theorem exec_block_append_prefix_error
    (fuel k : Nat) (left right : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (err : EvmYul.Yul.Exception)
    (hLeft :
      EvmYul.Yul.exec (fuel + left.length + k) (.Block left) codeOverride state =
        .error err) :
    EvmYul.Yul.exec (fuel + left.length + k) (.Block (left ++ right))
      codeOverride state = .error err := by
  induction left generalizing fuel state with
  | nil =>
      generalize hFuel : fuel + k = remaining at hLeft ⊢
      cases remaining with
      | zero =>
          simpa [hFuel, EvmYul.Yul.exec] using hLeft
      | succ remaining' =>
          have hLeftS :
              EvmYul.Yul.exec (Nat.succ remaining') (.Block [])
                codeOverride state = .error err := by
            simpa [hFuel] using hLeft
          simp [EvmYul.Yul.exec] at hLeftS
  | cons stmt rest ih =>
      have hFuel :
          fuel + (stmt :: rest).length + k = fuel + rest.length + k + 1 := by
        simp only [List.length_cons]; omega
      have hLeft' :
          EvmYul.Yul.exec (Nat.succ (fuel + rest.length + k))
            (.Block (stmt :: rest)) codeOverride state = .error err := by
        simpa [hFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLeft
      simp only [EvmYul.Yul.exec] at hLeft'
      generalize hHead :
        EvmYul.Yul.exec (fuel + rest.length + k) stmt codeOverride state = head
        at hLeft'
      cases head with
      | error err' =>
          simp at hLeft'
          subst err'
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state err hHead)
      | ok next =>
          simp at hLeft'
          have hTail :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block rest)
                codeOverride next = .error err := hLeft'
          have hRest :
              EvmYul.Yul.exec (fuel + rest.length + k) (.Block (rest ++ right))
                codeOverride next = .error err :=
            ih fuel next hTail
          have hGoalFuel :
              fuel + rest.length + k + 1 = fuel + (stmt :: rest).length + k := by
            simp only [List.length_cons]; omega
          simpa [hGoalFuel, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using
              (exec_block_cons_tail_error (fuel + rest.length + k)
                stmt (rest ++ right) codeOverride state next err hHead hRest)

theorem exec_block_nil_ok
    (fuel' : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel') (.Block []) codeOverride state =
      .ok state := by
  simp [EvmYul.Yul.exec]

theorem exec_block_nil_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10) (.Block []) codeOverride state =
      .ok state := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (exec_block_nil_ok (fuel + suffixLen + 9) codeOverride state)

theorem exec_block_leave_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10) (.Block [.Leave]) codeOverride
        state =
      .ok (state.setLeave) := by
  have hFuel :
      fuel + suffixLen + 10 = Nat.succ (Nat.succ (fuel + suffixLen + 8)) := by
    omega
  rw [hFuel]
  cases state <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]

/-- Executing the native lowering of a source `.block [.leave]` user body.

`[.block [.leave]]` lowers to `[.Block [.Leave]]`; wrapped in the outer
dispatcher block this becomes `.Block [.Block [.Leave]]`. The inner `.Leave`
sets the leave flag on the underlying state, the inner block continues with
its empty tail, and the outer block likewise continues with an empty tail —
so the whole expression evaluates to `.ok state.setLeave`, identical to the
flat `.Block [.Leave]` case but consuming two extra fuel for the nested
block layer. -/
theorem exec_block_block_leave_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10) (.Block [.Block [.Leave]])
        codeOverride state =
      .ok (state.setLeave) := by
  have hFuel :
      fuel + suffixLen + 10 =
        Nat.succ (Nat.succ (Nat.succ (Nat.succ (fuel + suffixLen + 6)))) := by
    omega
  rw [hFuel]
  cases state <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]

/-- Executing the native lowering of a source `[.block [], .leave]` user body
(F2's body shape).

`[.block [], .leave]` lowers to `[.Block [], .Leave]`; wrapped in the outer
dispatcher block this becomes `.Block [.Block [], .Leave]`. The inner
`.Block []` is a no-op head, the outer block continues with `.Leave`, and the
final state is `state.setLeave`. Mirrors `exec_block_block_leave_ok_add_ten`
but with a leading `.Block []` no-op instead of a wrapping `.Block`. -/
theorem exec_block_label_prefix_leave_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10) (.Block [.Block [], .Leave])
        codeOverride state =
      .ok (state.setLeave) := by
  have hFuel :
      fuel + suffixLen + 10 =
        Nat.succ (Nat.succ (Nat.succ (Nat.succ (fuel + suffixLen + 6)))) := by
    omega
  rw [hFuel]
  cases state <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]

/-- Executing the native lowering of a source `[.block [], .block [.leave]]`
user body (F4's body shape).

`[.block [], .block [.leave]]` lowers to `[.Block [], .Block [.Leave]]`;
wrapped in the outer dispatcher block this becomes
`.Block [.Block [], .Block [.Leave]]`. The leading `.Block []` is a no-op, the
inner `.Block [.Leave]` sets the leave flag, and the final state is
`state.setLeave`. -/
theorem exec_block_label_prefix_block_leave_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10)
        (.Block [.Block [], .Block [.Leave]]) codeOverride state =
      .ok (state.setLeave) := by
  have hFuel :
      fuel + suffixLen + 10 =
        Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ
          (fuel + suffixLen + 4)))))) := by
    omega
  rw [hFuel]
  cases state <;> simp [EvmYul.Yul.exec, EvmYul.Yul.State.setLeave]

/-- Executing the native lowering of a source `.block []` user body.

`[.block []]` lowers to `[.Block []]`; wrapped in the outer dispatcher block
this becomes `.Block [.Block []]`. Both blocks fall through their empty
contents without setting the leave flag, so the whole expression evaluates to
`.ok state`. Mirrors `exec_block_block_leave_ok_add_ten` but with no inner
`.Leave` statement. -/
theorem exec_block_block_nil_ok_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10) (.Block [.Block []])
        codeOverride state =
      .ok state := by
  have hFuel :
      fuel + suffixLen + 10 =
        Nat.succ (Nat.succ (Nat.succ (fuel + suffixLen + 7))) := by
    omega
  rw [hFuel]
  cases state <;> simp [EvmYul.Yul.exec]

theorem exec_block_stop_halt_add_ten
    (fuel suffixLen : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + suffixLen + 10)
        (.Block [.ExprStmtCall (Backends.lowerExprNative (.call "stop" []))])
        codeOverride state =
      .error (EvmYul.Yul.Exception.YulHalt state ⟨0⟩) := by
  have hFuel :
      fuel + suffixLen + 10 =
        Nat.succ (Nat.succ (Nat.succ (fuel + suffixLen + 7))) := by
    omega
  rw [Backends.lowerExprNative_call_runtimePrimOp "stop" []
    EvmYul.Operation.STOP (by rfl)]
  rw [hFuel]
  simp [EvmYul.Yul.exec, EvmYul.Yul.execPrimCall, EvmYul.Yul.evalArgs,
    EvmYul.Yul.reverse', EvmYul.Yul.multifill']

/-- Peel the no-op native statement emitted for a source Yul comment.

Lowering `.comment` produces `.Block []`; this lemma removes that head block
from an enclosing native block while accounting for the two positive fuel
steps needed by the outer cons and the inner empty block. -/
theorem exec_block_noop_block_head_eq
    (fuel : Nat)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ (Nat.succ fuel))
        (.Block (.Block [] :: rest)) codeOverride state =
      EvmYul.Yul.exec (Nat.succ fuel) (.Block rest) codeOverride state :=
  exec_block_cons_ok_eq (Nat.succ fuel) (.Block []) rest codeOverride state
    state (exec_block_nil_ok fuel codeOverride state)

def nativeSwitchHasSelectorName : EvmYul.Identifier := "__has_selector"

def nativeSwitchPrefixStmts
    (discrName matchedName : EvmYul.Identifier) :
    List EvmYul.Yul.Ast.Stmt :=
  [.Let [discrName]
    (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)),
   .Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]

def nativeSwitchInitialOkState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.State :=
  .Ok (initialState contract tx storage observableSlots).sharedState ∅

def nativeSwitchPostInitFreeMemorySharedState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.SharedState .Yul :=
  { (initialState contract tx storage observableSlots).sharedState with
    toMachineState :=
      (initialState contract tx storage observableSlots).sharedState.toMachineState.mstore
        (EvmYul.UInt256.ofNat Compiler.Constants.freeMemoryPointer)
        (EvmYul.UInt256.ofNat 128) }

def nativeSwitchPostInitFreeMemoryState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore) :
    EvmYul.Yul.State :=
  .Ok (nativeSwitchPostInitFreeMemorySharedState contract tx storage observableSlots)
    store

/-- Execute the exact generated `initFreeMemoryPointer` native statement from
    a generated-runtime dispatcher initial state. This is deliberately narrow:
    it records only the concrete memory update performed by
    `mstore(freeMemoryPointer, 128)`. -/
theorem exec_initFreeMemoryPointer_head_ok
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.exec (fuel + 6)
      (.ExprStmtCall
        (Backends.lowerExprNative
          (Yul.YulExpr.call "mstore"
            [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
              Yul.YulExpr.lit 128])))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPostInitFreeMemoryState contract tx storage
      observableSlots ∅) := by
  convert exec_lowerExprNative_mstore_lit_lit_ok_fuel
      fuel
      (initialState contract tx storage observableSlots).sharedState
      (∅ : EvmYul.Yul.VarStore)
      (some contract)
      Compiler.Constants.freeMemoryPointer 128 using 1 <;>
    simp [nativeSwitchInitialOkState, nativeSwitchPostInitFreeMemoryState,
      nativeSwitchPostInitFreeMemorySharedState, EvmYul.SharedState.toState,
      EvmYul.Yul.State.toMachineState]

/-- Peel the exact generated `initFreeMemoryPointer` head from a dispatcher
    block, exposing the residual dispatcher execution on the concrete
    post-`mstore(freeMemoryPointer, 128)` state. -/
theorem exec_block_cons_initFreeMemoryPointer_eq
    (fuel : Nat)
    (rest : List EvmYul.Yul.Ast.Stmt)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat) :
    EvmYul.Yul.exec (Nat.succ (fuel + 6))
      (.Block
        (.ExprStmtCall
          (Backends.lowerExprNative
            (Yul.YulExpr.call "mstore"
              [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
                Yul.YulExpr.lit 128])) :: rest))
      (some contract)
      (nativeSwitchInitialOkState contract tx storage observableSlots) =
    EvmYul.Yul.exec (fuel + 6) (.Block rest) (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage
        observableSlots ∅) :=
  exec_block_cons_ok_eq (fuel + 6)
    (.ExprStmtCall
      (Backends.lowerExprNative
        (Yul.YulExpr.call "mstore"
          [Yul.YulExpr.lit Compiler.Constants.freeMemoryPointer,
            Yul.YulExpr.lit 128])))
    rest (some contract)
    (nativeSwitchInitialOkState contract tx storage observableSlots)
    (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots ∅)
    (exec_initFreeMemoryPointer_head_ok fuel contract tx storage observableSlots)

/-- Post-generated-init variant of
    `exec_let_lowerExprNative_selectorExpr_initialState_store_ok_fuel`.
    The `initFreeMemoryPointer` head only writes EVM memory, so the generated
    selector expression still decodes the same calldata selector while
    preserving the explicit varstore. -/
theorem exec_let_lowerExprNative_selectorExpr_postInitFreeMemory_store_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [discrName]
          (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          store) =
      .ok ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots store).insert discrName
        (EvmYul.UInt256.ofNat
          (tx.functionSelector % Compiler.Constants.selectorModulus))) := by
  have hv :=
    initialState_selectorExpr_native_uint256 contract tx storage observableSlots
  have hv224 :
      EvmYul.UInt256.shiftRight
        (EvmYul.State.calldataload
          (EvmYul.SharedState.toState
            (nativeSwitchPostInitFreeMemorySharedState contract tx storage
              observableSlots))
          (EvmYul.UInt256.ofNat 0))
        (EvmYul.UInt256.ofNat 224) =
      EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus) := by
    simpa [nativeSwitchPostInitFreeMemorySharedState,
      Compiler.Constants.selectorShift, EvmYul.SharedState.toState,
      EvmYul.Yul.State.toMachineState] using hv
  rw [lowerExprNative_selectorExpr]
  simp [nativeSwitchPostInitFreeMemoryState, EvmYul.Yul.exec,
    EvmYul.Yul.eval, EvmYul.Yul.evalArgs, EvmYul.Yul.evalTail,
    EvmYul.Yul.evalPrimCall, EvmYul.Yul.execPrimCall, EvmYul.Yul.reverse',
    EvmYul.Yul.cons', EvmYul.Yul.head', EvmYul.Yul.multifill',
    EvmYul.Yul.State.multifill, Compiler.Constants.selectorShift]
  rw [hv224]

/-- Post-generated-init variant of the `__has_selector` binding. The generated
    init head only changes memory, leaving calldata size unchanged. -/
theorem exec_let_lowerExprNative_iszero_lt_calldatasize_4_postInitFreeMemory_store_ok_fuel
    (fuel : Nat)
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          store) =
      .ok ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots store).insert name (EvmYul.UInt256.ofNat 1)) := by
  change EvmYul.Yul.exec (fuel + 11)
        (.Let [name]
          (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero"
              [Yul.YulExpr.call "lt"
                [Yul.YulExpr.call "calldatasize" [],
                 Yul.YulExpr.lit 4]]))))
        (some contract)
        (.Ok (nativeSwitchPostInitFreeMemorySharedState contract tx storage
          observableSlots) store) =
      .ok (((.Ok (nativeSwitchPostInitFreeMemorySharedState contract tx storage
          observableSlots) store : EvmYul.Yul.State).insert name
        (EvmYul.UInt256.ofNat 1)))
  rw [exec_let_lowerExprNative_iszero_lt_calldatasize_4_ok_fuel]
  simp [nativeSwitchPostInitFreeMemorySharedState, calldataToByteArray_size,
    uint256_lt_ofNat_4_eq_zero_of_ge _ (by omega) hNoWrap,
    uint256_isZero_ofNat_zero]

private theorem nativeSwitchPostInitFreeMemoryState_insert_lookup_self
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    ((nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
        store).insert name value)[name]! = value := by
  simp [nativeSwitchPostInitFreeMemoryState, EvmYul.Yul.State.insert,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem,
    EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

def nativeSwitchPrefixFinalState
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.State :=
  ((nativeSwitchInitialOkState contract tx storage observableSlots).insert discrName
    (EvmYul.UInt256.ofNat
      (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
    matchedName (EvmYul.UInt256.ofNat 0)

/-- The generated dispatcher switch prefix initializes the discriminator temp
    from native calldata selector evaluation, then clears the lazy matched flag.

This packages the first two statements emitted by `lowerNativeSwitchBlock` for
the generated dispatcher case and leaves the remaining case-chain proof with a
state whose native switch temporaries are aligned to the EVMYulLean fuel wrapper. -/
theorem exec_nativeSwitchPrefix_selector_initialState_ok
    (contract : EvmYul.Yul.Ast.YulContract)
    (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord)
    (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec 12
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName) := by
  let initState : EvmYul.Yul.State :=
    nativeSwitchInitialOkState contract tx storage observableSlots
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec 12
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  rw [nativeSwitchPrefixStmts]
  apply exec_block_cons_ok 11
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_ok
      contract tx storage observableSlots discrName
  · apply exec_block_cons_ok 10
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp
      simp [matchedState]
    · simp [EvmYul.Yul.exec]

theorem exec_nativeSwitchPrefix_selector_initialState_ok_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) (nativeSwitchInitialOkState contract tx storage observableSlots) =
    .ok (nativeSwitchPrefixFinalState contract tx storage observableSlots
      discrName matchedName) := by
  let initState : EvmYul.Yul.State :=
    nativeSwitchInitialOkState contract tx storage observableSlots
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  have hFuel : fuel + 12 = Nat.succ (fuel + 11) := by omega
  rw [hFuel]
  rw [nativeSwitchPrefixStmts]
  apply exec_block_cons_ok (fuel + 11)
        (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
        [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_ok_fuel
      fuel contract tx storage observableSlots discrName
  · have hFuelTail : fuel + 11 = Nat.succ (fuel + 10) := by omega
    rw [hFuelTail]
    apply exec_block_cons_ok (fuel + 10)
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp [matchedState]
    · simp [EvmYul.Yul.exec]

/-- Store-parametric form of `exec_nativeSwitchPrefix_selector_initialState_ok_fuel`.
    The two prefix Lets only depend on calldata (read-only via the shared
    state), so they are invariant under any preceding native varstore. Lifts
    the dispatcher prefix execution to a state already carrying additional
    bindings (e.g. the buildSwitch wrapper's `__has_selector := 1`). -/
theorem exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract)
      (.Ok (initialState contract tx storage observableSlots).sharedState store) =
    .ok (((.Ok (initialState contract tx storage observableSlots).sharedState store
            : EvmYul.Yul.State).insert discrName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          matchedName (EvmYul.UInt256.ofNat 0)) := by
  let initState : EvmYul.Yul.State :=
    .Ok (initialState contract tx storage observableSlots).sharedState store
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  have hFuel : fuel + 12 = Nat.succ (fuel + 11) := by omega
  rw [hFuel, nativeSwitchPrefixStmts]
  apply exec_block_cons_ok (fuel + 11)
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_initialState_store_ok_fuel
      fuel contract tx storage observableSlots store discrName
  · have hFuelTail : fuel + 11 = Nat.succ (fuel + 10) := by omega
    rw [hFuelTail]
    apply exec_block_cons_ok (fuel + 10)
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp [matchedState]
    · simp [EvmYul.Yul.exec]

/-- Post-generated-init variant of
    `exec_nativeSwitchPrefix_selector_initialState_store_ok_fuel`. The native
    switch prefix reads the calldata selector and writes only the two generated
    switch temporaries, so it can start from the exact state produced by
    `initFreeMemoryPointer`. -/
theorem exec_nativeSwitchPrefix_selector_postInitFreeMemory_store_ok_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (discrName matchedName : EvmYul.Identifier) :
    EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract)
      (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
        store) =
    .ok (((nativeSwitchPostInitFreeMemoryState contract tx storage
            observableSlots store).insert discrName
            (EvmYul.UInt256.ofNat
              (tx.functionSelector % Compiler.Constants.selectorModulus))).insert
          matchedName (EvmYul.UInt256.ofNat 0)) := by
  let initState : EvmYul.Yul.State :=
    nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots store
  let discrState : EvmYul.Yul.State :=
    initState.insert discrName
      (EvmYul.UInt256.ofNat
        (tx.functionSelector % Compiler.Constants.selectorModulus))
  let matchedState : EvmYul.Yul.State :=
    discrState.insert matchedName (EvmYul.UInt256.ofNat 0)
  change EvmYul.Yul.exec (fuel + 12)
      (.Block (nativeSwitchPrefixStmts discrName matchedName))
      (some contract) initState = .ok matchedState
  have hFuel : fuel + 12 = Nat.succ (fuel + 11) := by omega
  rw [hFuel, nativeSwitchPrefixStmts]
  apply exec_block_cons_ok (fuel + 11)
      (.Let [discrName]
        (some (Backends.lowerExprNative Compiler.Proofs.YulGeneration.selectorExpr)))
      [.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0)))]
      (some contract) initState discrState matchedState
  · exact exec_let_lowerExprNative_selectorExpr_postInitFreeMemory_store_ok_fuel
      fuel contract tx storage observableSlots store discrName
  · have hFuelTail : fuel + 11 = Nat.succ (fuel + 10) := by omega
    rw [hFuelTail]
    apply exec_block_cons_ok (fuel + 10)
        (.Let [matchedName] (some (.Lit (EvmYul.UInt256.ofNat 0))))
        [] (some contract) discrState matchedState matchedState
    · simp [matchedState]
    · simp [EvmYul.Yul.exec]

/-- Native `if` reduction for a zero guard. -/
theorem exec_if_eval_zero
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (hEval :
      EvmYul.Yul.eval fuel' cond codeOverride state =
        .ok (next, (⟨0⟩ : EvmYul.Literal))) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .ok next := by
  simp [EvmYul.Yul.exec, hEval]

/-- Native `if` reduction for a nonzero guard. -/
theorem exec_if_eval_nonzero
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next final : EvmYul.Yul.State)
    (value : EvmYul.Literal)
    (hEval : EvmYul.Yul.eval fuel' cond codeOverride state = .ok (next, value))
    (hNe : value ≠ (⟨0⟩ : EvmYul.Literal))
    (hBody : EvmYul.Yul.exec fuel' (.Block body) codeOverride next = .ok final) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .ok final := by
  simp [EvmYul.Yul.exec, hEval, hNe, hBody]

/-- Native `if` reduction for a nonzero guard when the body halts or errors. -/
theorem exec_if_eval_nonzero_error
    (fuel' : Nat)
    (cond : EvmYul.Yul.Ast.Expr)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state next : EvmYul.Yul.State)
    (value : EvmYul.Literal)
    (err : EvmYul.Yul.Exception)
    (hEval : EvmYul.Yul.eval fuel' cond codeOverride state = .ok (next, value))
    (hNe : value ≠ (⟨0⟩ : EvmYul.Literal))
    (hBody : EvmYul.Yul.exec fuel' (.Block body) codeOverride next = .error err) :
    EvmYul.Yul.exec (Nat.succ fuel') (.If cond body) codeOverride state =
      .error err := by
  simp [EvmYul.Yul.exec, hEval, hNe, hBody]

/-- Native `if` execution skips the lowered selector-miss revert guard
    `if iszero(<name>) { … }` whenever the named variable is bound to
    `UInt256.ofNat 1` — i.e., when the dispatcher's `let __has_selector :=
    iszero(lt(calldatasize(), 4))` step has bound the variable to one
    (which `exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok`
    establishes for any tx satisfying the calldata-size no-wrap bound).
    This is the per-statement no-op for the dispatcher's `If1` step that
    lets the selector-hit `If2` body fire on the same incoming state. -/
theorem exec_if_lowerExprNative_iszero_ident_one_skip
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 9
        (.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident (name : String)]))
          body)
        codeOverride state =
      .ok state :=
  exec_if_eval_zero 8 _ body codeOverride state state
    (eval_lowerExprNative_iszero_ident_one_ok state codeOverride name hVal)

/-- Native `if` execution skips the lowered `callvalue()` revert guard
    `if callvalue() { … }` whenever the current `executionEnv.weiValue` is
    the canonical zero literal — i.e., when the transaction's `msgValue` is
    `0`. This is the per-statement no-op for the dispatcher's hit-case
    body callvalue guard, mirroring `exec_if_lowerExprNative_iszero_ident_one_skip`
    for the selector-miss case. -/
theorem exec_if_lowerExprNative_callvalue_skip_zero_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (hWei : shared.executionEnv.weiValue = (⟨0⟩ : EvmYul.Literal)) :
    EvmYul.Yul.exec (fuel + 6)
        (.If (Backends.lowerExprNative (Yul.YulExpr.call "callvalue" [])) body)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store) := by
  refine exec_if_eval_zero (fuel + 5) _ body codeOverride
    (.Ok shared store) (.Ok shared store) ?_
  rw [eval_lowerExprNative_callvalue_ok_fuel, hWei]

/-- A native `UInt256` literal is zero whenever the source Nat is zero modulo
the EVM word modulus. -/
theorem natToUInt256_eq_zero_of_mod_evm
    (n : Nat) (hZero : n % evmModulus = 0) :
    natToUInt256 n = (⟨0⟩ : EvmYul.Literal) := by
  have hZero' : n % EvmYul.UInt256.size = 0 := by
    simpa [evmModulus, EvmYul.UInt256.size] using hZero
  change EvmYul.UInt256.ofNat n = EvmYul.UInt256.ofNat 0
  unfold EvmYul.UInt256.ofNat
  simp [Id.run, Fin.ofNat, hZero']

/-- A native `UInt256` literal is nonzero whenever the source Nat is nonzero
modulo the EVM word modulus. -/
theorem natToUInt256_ne_zero_of_mod_ne
    (n : Nat) (hNonzero : n % evmModulus ≠ 0) :
    natToUInt256 n ≠ (⟨0⟩ : EvmYul.Literal) := by
  intro h
  have hVal : n % EvmYul.UInt256.size = 0 := by
    have hCong := congrArg (fun u : EvmYul.UInt256 => u.val.val) h
    simpa [natToUInt256, EvmYul.UInt256.ofNat, Id.run, Fin.ofNat] using hCong
  exact hNonzero (by simpa [evmModulus, EvmYul.UInt256.size] using hVal)

/-- In the non-payable branch, `DispatchGuardsSafe` supplies the exact modular
zero fact needed to skip the lowered native `callvalue()` guard. -/
theorem DispatchGuardsSafe_msgValue_zero_mod_of_nonpayable
    (fn : IRFunction) (tx : IRTransaction)
    (hguards : DispatchGuardsSafe fn tx)
    (hNonPayable : fn.payable = false) :
    tx.msgValue % evmModulus = 0 := by
  rcases hguards with ⟨hValueSafe, _⟩
  rcases hValueSafe with hPayable | hZero
  · cases (by simp [hNonPayable] at hPayable : False)
  · exact hZero

/-- `DispatchGuardsSafe` records that the generated ABI calldata-size guard
threshold fits in a native EVM word. -/
theorem DispatchGuardsSafe_calldata_threshold_lt
    (fn : IRFunction) (tx : IRTransaction)
    (hguards : DispatchGuardsSafe fn tx) :
    4 + fn.params.length * 32 < EvmYul.UInt256.size := by
  exact by
    simpa [evmModulus, EvmYul.UInt256.size] using hguards.2

/-- General-`k` form of `uint256_lt_ofNat_4_eq_zero_of_ge`: when `k ≤ n` and
    both fit in `UInt256`, the EVMYulLean primitive `LT(ofNat n, ofNat k)`
    evaluates to the canonical zero word. Used to discharge the
    lt-calldatasize-guard on the body's inner argument-length revert. -/
private theorem uint256_lt_ofNat_eq_zero_of_ge
    (n k : Nat) (hLe : k ≤ n)
    (hSize : n < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size) :
    EvmYul.UInt256.lt (EvmYul.UInt256.ofNat n) (EvmYul.UInt256.ofNat k) =
      EvmYul.UInt256.ofNat 0 := by
  have hN : (EvmYul.UInt256.ofNat n).val.val = n := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hSize]
  have hK : (EvmYul.UInt256.ofNat k).val.val = k := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hKSize]
  have hNotLt : ¬ ((EvmYul.UInt256.ofNat n : EvmYul.UInt256) <
      (EvmYul.UInt256.ofNat k : EvmYul.UInt256)) := by
    intro hLt
    have hh : (EvmYul.UInt256.ofNat n).val.val <
        (EvmYul.UInt256.ofNat k).val.val := hLt
    rw [hN, hK] at hh
    omega
  simp [EvmYul.UInt256.lt, hNotLt]

/-- General-`k` positive form of the native `LT(ofNat n, ofNat k)` primitive:
when `n < k` and both values fit in `UInt256`, the EVMYulLean primitive
evaluates to the canonical one word. -/
private theorem uint256_lt_ofNat_eq_one_of_lt
    (n k : Nat) (hLt : n < k)
    (hSize : n < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size) :
    EvmYul.UInt256.lt (EvmYul.UInt256.ofNat n) (EvmYul.UInt256.ofNat k) =
      EvmYul.UInt256.ofNat 1 := by
  have hN : (EvmYul.UInt256.ofNat n).val.val = n := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hSize]
  have hK : (EvmYul.UInt256.ofNat k).val.val = k := by
    unfold EvmYul.UInt256.ofNat
    simp [Id.run, Fin.ofNat, Nat.mod_eq_of_lt hKSize]
  have hWordLt :
      (EvmYul.UInt256.ofNat n : EvmYul.UInt256) <
        (EvmYul.UInt256.ofNat k : EvmYul.UInt256) := by
    change (EvmYul.UInt256.ofNat n).val.val <
      (EvmYul.UInt256.ofNat k).val.val
    rw [hN, hK]
    exact hLt
  simp [EvmYul.UInt256.lt, hWordLt]

/-- Native `if` execution skips the lowered `if lt(calldatasize(), k) { … }`
    revert guard whenever the current calldata is at least `k` bytes — i.e.,
    when the caller has supplied enough calldata for the function's selector
    plus its declared arguments. This is the per-statement no-op for the
    dispatcher's hit-case body inner argument-length guard, mirroring
    `exec_if_lowerExprNative_callvalue_skip_zero_fuel` for the callvalue
    guard. -/
theorem exec_if_lowerExprNative_lt_calldatasize_skip_ge_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hGe : k ≤ shared.executionEnv.calldata.size) :
    EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
                (Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [],
                   Yul.YulExpr.lit k]))
          body)
        codeOverride (.Ok shared store) =
      .ok (.Ok shared store) := by
  refine exec_if_eval_zero (fuel + 8) _ body codeOverride
    (.Ok shared store) (.Ok shared store) ?_
  rw [eval_lowerExprNative_lt_calldatasize_ok_fuel,
      uint256_lt_ofNat_eq_zero_of_ge _ _ hGe hSize hKSize]
  rfl

/-- Native `if` execution takes the lowered `if lt(calldatasize(), k) { … }`
    revert guard whenever the current calldata is shorter than `k` bytes. -/
theorem exec_if_lowerExprNative_lt_calldatasize_take_lt_revert_fuel
    (fuel : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (k : Nat)
    (hSize : shared.executionEnv.calldata.size < EvmYul.UInt256.size)
    (hKSize : k < EvmYul.UInt256.size)
    (hLt : shared.executionEnv.calldata.size < k) :
    EvmYul.Yul.exec (fuel + 9)
        (.If (Backends.lowerExprNative
                (Yul.YulExpr.call "lt"
                  [Yul.YulExpr.call "calldatasize" [],
                   Yul.YulExpr.lit k]))
          [nativeRevertZeroZeroStmt])
        codeOverride (.Ok shared store) =
      .error EvmYul.Yul.Exception.Revert := by
  have hEval :
      EvmYul.Yul.eval (fuel + 8)
          (Backends.lowerExprNative
            (Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [],
               Yul.YulExpr.lit k]))
          codeOverride (.Ok shared store) =
        .ok (.Ok shared store, EvmYul.UInt256.ofNat 1) := by
    rw [eval_lowerExprNative_lt_calldatasize_ok_fuel,
      uint256_lt_ofNat_eq_one_of_lt _ _ hLt hSize hKSize]
  have hBody :
      EvmYul.Yul.exec (fuel + 8) (.Block [nativeRevertZeroZeroStmt])
          codeOverride (.Ok shared store) =
        .error EvmYul.Yul.Exception.Revert := by
    have hFuel : fuel + 8 = Nat.succ (fuel + 7) := by omega
    rw [hFuel]
    exact exec_block_cons_error (fuel + 7) nativeRevertZeroZeroStmt []
      codeOverride (.Ok shared store) EvmYul.Yul.Exception.Revert
      (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (exec_revert_zero_zero_error (fuel + 1) (.Ok shared store)
            codeOverride))
  have hFuel : fuel + 9 = Nat.succ (fuel + 8) := by omega
  rw [hFuel]
  exact exec_if_eval_nonzero_error (fuel + 8)
    (Backends.lowerExprNative
      (Yul.YulExpr.call "lt"
        [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit k]))
    [nativeRevertZeroZeroStmt] codeOverride (.Ok shared store)
    (.Ok shared store) (EvmYul.UInt256.ofNat 1)
    EvmYul.Yul.Exception.Revert hEval
    (by decide) hBody

/-- Fuel-parametric form of `exec_if_lowerExprNative_iszero_ident_one_skip`. -/
theorem exec_if_lowerExprNative_iszero_ident_one_skip_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
        (.If
          (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident (name : String)]))
          body)
        codeOverride state =
      .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_lowerExprNative_iszero_ident_one_ok_fuel fuel state codeOverride name hVal))

/-- Lookup of a freshly inserted name in the empty-store `nativeSwitchInitialOkState`
    is the inserted value; mediates between the post-`Let` post state produced
    by the selector-binding lemma and the `hVal` premise consumed by the
    `If1`-skip lemma. -/
theorem nativeSwitchInitialOkState_insert_lookup_self
    (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (name : EvmYul.Identifier) (value : EvmYul.UInt256) :
    ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
        name value)[name]! = value := by
  simp [nativeSwitchInitialOkState, EvmYul.Yul.State.insert,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem,
    EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

/-- Fuel-parametric native `If` reduction for the lowered selector-hit guard
    `if __has_selector { … }`: when the named variable is bound to
    `UInt256.ofNat 1`, the lowered `Var name` condition evaluates non-zero so
    the if-statement reduces to executing its body block at strictly smaller
    fuel on the same incoming state. This is the dispatcher's `If2`-take
    counterpart of the `If1`-skip lemma. -/
theorem exec_if_lowerExprNative_ident_one_take_fuel
    (fuel : Nat) (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) (name : EvmYul.Identifier)
    (hVal : state[name]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 2)
        (.If (Backends.lowerExprNative (Yul.YulExpr.ident (name : String))) body)
        codeOverride state =
      EvmYul.Yul.exec (fuel + 1) (.Block body) codeOverride state := by
  have hNe : (EvmYul.UInt256.ofNat 1 : EvmYul.UInt256) ≠ ⟨0⟩ := by decide
  simp [EvmYul.Yul.exec, Backends.lowerExprNative, EvmYul.Yul.eval, hVal, hNe]
  intro hZero
  exact (hNe (hVal.symm.trans hZero)).elim

/-- Native singleton-block exec equals the inner statement exec at decremented
    fuel: the trailing `Block []` peel always succeeds at positive fuel and
    returns the head-statement result unchanged, so for any positive outer
    fuel the singleton-block is the inner statement. -/
theorem exec_block_singleton_eq
    (fuel : Nat) (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (fuel + 2) (.Block [stmt]) codeOverride state =
      EvmYul.Yul.exec (fuel + 1) stmt codeOverride state := by
  cases h : EvmYul.Yul.exec (fuel + 1) stmt codeOverride state with
  | error e => simp [EvmYul.Yul.exec, h]
  | ok s' =>
      cases s' <;> simp [EvmYul.Yul.exec, h]

/-- Native dispatcher inner-block chain peel of `Let` + `If1`-skip on
    `nativeSwitchInitialOkState`: under the calldata no-wrap bound, the
    selector-binding `Let` runs to `__has_selector ↦ 1` and the selector-miss
    `If1` body is statically skipped, so the outer block exec equals the
    residual `Block tail` exec at strictly smaller fuel on the post-`Let`
    state. Composes the existing `Let` and `If1`-skip fuel lemmas through
    `nativeSwitchInitialOkState_insert_lookup_self`. -/
theorem exec_block_letSelector_if1Skip_initialState_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (selectorName : EvmYul.Identifier) (if1Body tail : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          tail))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          selectorName (EvmYul.UInt256.ofNat 1)) := by
  simp only [nativeSwitchInitialOkState]
  have hLet := exec_let_lowerExprNative_iszero_lt_calldatasize_4_initialState_ok_fuel
    fuel contract tx storage observableSlots selectorName hNoWrap
  have hLookup := nativeSwitchInitialOkState_insert_lookup_self
    contract tx storage observableSlots selectorName (EvmYul.UInt256.ofNat 1)
  simp only [nativeSwitchInitialOkState] at hLookup
  have hIfRaw := exec_if_lowerExprNative_iszero_ident_one_skip_fuel
    (fuel + 1) if1Body (some contract) _ selectorName hLookup
  have hFuelEq : (fuel + 1) + 9 = fuel + 10 := by omega
  rw [hFuelEq] at hIfRaw
  rw [show fuel + 12 = (fuel + 11).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hLet,
      show fuel + 11 = (fuel + 10).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hIfRaw]

/-- Native dispatcher full inner-block 3-statement peel on
    `nativeSwitchInitialOkState`: under the calldata no-wrap bound, the
    selector-binding `Let` runs, the selector-miss `If1` is statically
    skipped, and the selector-hit `If2` is taken, leaving the residual
    `Block if2Body` exec at strictly smaller fuel on the post-`Let` state.
    Composes `exec_block_letSelector_if1Skip_initialState_fuel` with the
    `exec_block_singleton_eq` and `exec_if_lowerExprNative_ident_one_take_fuel`
    lemmas through `nativeSwitchInitialOkState_insert_lookup_self`. -/
theorem exec_block_letSelector_if1Skip_if2Take_initialState_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (selectorName : EvmYul.Identifier)
    (if1Body if2Body : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          [.If (Backends.lowerExprNative
              (Yul.YulExpr.ident selectorName)) if2Body]))
        (some contract)
        (nativeSwitchInitialOkState contract tx storage observableSlots) =
      EvmYul.Yul.exec (fuel + 8) (.Block if2Body) (some contract)
        ((nativeSwitchInitialOkState contract tx storage observableSlots).insert
          selectorName (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_block_letSelector_if1Skip_initialState_fuel fuel contract tx storage
        observableSlots selectorName if1Body
        [.If (Backends.lowerExprNative (Yul.YulExpr.ident selectorName)) if2Body]
        hNoWrap]
  have hLookup := nativeSwitchInitialOkState_insert_lookup_self
    contract tx storage observableSlots selectorName (EvmYul.UInt256.ofNat 1)
  rw [show fuel + 10 = (fuel + 8) + 2 from rfl,
      exec_block_singleton_eq (fuel + 8) _ (some contract) _,
      show fuel + 8 + 1 = (fuel + 7) + 2 from rfl,
      exec_if_lowerExprNative_ident_one_take_fuel (fuel + 7) if2Body
        (some contract) _ selectorName hLookup,
      show fuel + 7 + 1 = fuel + 8 from rfl]

/-- Post-generated-init variant of
    `exec_block_letSelector_if1Skip_initialState_fuel`. It starts from the
    explicit state produced by `initFreeMemoryPointer`, preserving the
    generated memory write while proving the same `__has_selector := 1`
    transition. -/
theorem exec_block_letSelector_if1Skip_postInitFreeMemory_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (selectorName : EvmYul.Identifier) (if1Body tail : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          tail))
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          store) =
      EvmYul.Yul.exec (fuel + 10) (.Block tail) (some contract)
        ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots store).insert selectorName (EvmYul.UInt256.ofNat 1)) := by
  have hLet :=
    exec_let_lowerExprNative_iszero_lt_calldatasize_4_postInitFreeMemory_store_ok_fuel
      fuel contract tx storage observableSlots store selectorName hNoWrap
  have hLookup := nativeSwitchPostInitFreeMemoryState_insert_lookup_self
    contract tx storage observableSlots store selectorName (EvmYul.UInt256.ofNat 1)
  have hIfRaw := exec_if_lowerExprNative_iszero_ident_one_skip_fuel
    (fuel + 1) if1Body (some contract) _ selectorName hLookup
  have hFuelEq : (fuel + 1) + 9 = fuel + 10 := by omega
  rw [hFuelEq] at hIfRaw
  rw [show fuel + 12 = (fuel + 11).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hLet,
      show fuel + 11 = (fuel + 10).succ from rfl,
      exec_block_cons_ok_eq _ _ _ _ _ _ hIfRaw]

/-- Post-generated-init variant of
    `exec_block_letSelector_if1Skip_if2Take_initialState_fuel`. This is the
    generated bridge from the init-prefixed runtime into the lazy native switch
    tail, with the `__has_selector` flag modeled as part of the transition. -/
theorem exec_block_letSelector_if1Skip_if2Take_postInitFreeMemory_fuel
    (fuel : Nat) (contract : EvmYul.Yul.Ast.YulContract) (tx : YulTransaction)
    (storage : IRStorageSlot → IRStorageWord) (observableSlots : List Nat)
    (store : EvmYul.Yul.VarStore)
    (selectorName : EvmYul.Identifier)
    (if1Body if2Body : List EvmYul.Yul.Ast.Stmt)
    (hNoWrap : 4 + tx.args.length * 32 < EvmYul.UInt256.size) :
    EvmYul.Yul.exec (fuel + 12)
        (.Block (.Let [selectorName] (some (Backends.lowerExprNative
            (Yul.YulExpr.call "iszero" [Yul.YulExpr.call "lt"
              [Yul.YulExpr.call "calldatasize" [], Yul.YulExpr.lit 4]]))) ::
          .If (Backends.lowerExprNative
              (Yul.YulExpr.call "iszero" [Yul.YulExpr.ident selectorName]))
            if1Body ::
          [.If (Backends.lowerExprNative
              (Yul.YulExpr.ident selectorName)) if2Body]))
        (some contract)
        (nativeSwitchPostInitFreeMemoryState contract tx storage observableSlots
          store) =
      EvmYul.Yul.exec (fuel + 8) (.Block if2Body) (some contract)
        ((nativeSwitchPostInitFreeMemoryState contract tx storage
          observableSlots store).insert selectorName (EvmYul.UInt256.ofNat 1)) := by
  rw [exec_block_letSelector_if1Skip_postInitFreeMemory_fuel fuel contract tx
        storage observableSlots store selectorName if1Body
        [.If (Backends.lowerExprNative (Yul.YulExpr.ident selectorName)) if2Body]
        hNoWrap]
  have hLookup := nativeSwitchPostInitFreeMemoryState_insert_lookup_self
    contract tx storage observableSlots store selectorName (EvmYul.UInt256.ofNat 1)
  rw [show fuel + 10 = (fuel + 8) + 2 from rfl,
      exec_block_singleton_eq (fuel + 8) _ (some contract) _,
      show fuel + 8 + 1 = (fuel + 7) + 2 from rfl,
      exec_if_lowerExprNative_ident_one_take_fuel (fuel + 7) if2Body
        (some contract) _ selectorName hLookup,
      show fuel + 7 + 1 = fuel + 8 from rfl]

/-- Native evaluation of the lazy lowered switch guard peels to the exact
    EVMYulLean `AND(ISZERO(matched), EQ(discr, tag))` value.

This is the next bridge after selector evaluation: selected-case execution can
now reason from concrete discriminator and matched-temporary bindings instead
of re-opening nested primitive-call evaluation. -/
theorem eval_nativeSwitchGuardedMatch_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state,
      EvmYul.UInt256.land
        (EvmYul.UInt256.isZero state[matchedName]!)
        (EvmYul.UInt256.eq state[discrName]! (EvmYul.UInt256.ofNat tag))) := by
  simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
    EvmYul.Yul.cons', EvmYul.Yul.head']
  rfl

/-- Fuel-parametric form of `eval_nativeSwitchGuardedMatch_ok`, for use under
    recursively executed generated switch blocks. -/
theorem eval_nativeSwitchGuardedMatch_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state,
      EvmYul.UInt256.land
        (EvmYul.UInt256.isZero state[matchedName]!)
        (EvmYul.UInt256.eq state[discrName]! (EvmYul.UInt256.ofNat tag))) := by
  cases fuel <;>
    simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
      EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
      EvmYul.Yul.cons', EvmYul.Yul.head'] <;> rfl

/-- The selected lowered switch case has a nonzero guard while no previous case
    has marked the switch matched and the discriminator equals the case tag. -/
theorem eval_nativeSwitchGuardedMatch_hit_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched, hDiscr]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero]
  decide

/-- An unmatched lowered switch case has a zero guard while no previous case has
    matched and the discriminator differs from the case tag. -/
theorem eval_nativeSwitchGuardedMatch_miss_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero, hDiscr]
  decide

/-- Fuel-parametric non-selected lowered switch case guard reduction. -/
theorem eval_nativeSwitchGuardedMatch_miss_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero, hDiscr]
  decide

/-- Bitwise `and` with a zero left operand stays zero for native UInt256 words. -/
private theorem uint256_land_zero_left (value : EvmYul.UInt256) :
    EvmYul.UInt256.land (EvmYul.UInt256.ofNat 0) value =
      EvmYul.UInt256.ofNat 0 := by
  cases value with
  | mk raw =>
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change (0 &&& (raw : Nat)) % EvmYul.UInt256.size = 0
    simp [Nat.zero_and]

private theorem uint256_land_zero_right (value : EvmYul.UInt256) :
    EvmYul.UInt256.land value (EvmYul.UInt256.ofNat 0) =
      EvmYul.UInt256.ofNat 0 := by
  cases value with
  | mk raw =>
    apply congrArg EvmYul.UInt256.mk
    apply Fin.ext
    change ((raw : Nat) &&& 0) % EvmYul.UInt256.size = 0
    simp [Nat.and_zero]

/-- Once the lazy lowered switch matched flag is set, later case guards evaluate
    to zero independently of the discriminator value. -/
theorem eval_nativeSwitchGuardedMatch_matched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 8
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok, hMatched]
  rw [show EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 1) =
      EvmYul.UInt256.ofNat 0 by decide]
  rw [uint256_land_zero_left]

/-- Fuel-parametric form of `eval_nativeSwitchGuardedMatch_matched_ok`. -/
theorem eval_nativeSwitchGuardedMatch_matched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched]
  rw [show EvmYul.UInt256.isZero (EvmYul.UInt256.ofNat 1) =
      EvmYul.UInt256.ofNat 0 by decide]
  rw [uint256_land_zero_left]

/-- Native `if` execution for the selected lowered switch case.  This packages
    guard evaluation with the existing nonzero-`if` reduction so the remaining
    case-chain proof can focus on matching/freshness invariants. -/
theorem exec_if_nativeSwitchGuardedMatch_hit
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody : EvmYul.Yul.exec 8 (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok final := by
  exact exec_if_eval_nonzero 8 _ body codeOverride state state final
    (EvmYul.UInt256.ofNat 1)
    (eval_nativeSwitchGuardedMatch_hit_ok state codeOverride discrName matchedName tag
      hMatched hDiscr)
    (by decide)
    hBody

/-- Native `if` execution skips a non-selected lowered switch case while no
    previous case has matched. -/
theorem exec_if_nativeSwitchGuardedMatch_miss
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  exact exec_if_eval_zero 8 _ body codeOverride state state
    (eval_nativeSwitchGuardedMatch_miss_ok state codeOverride discrName matchedName tag
      hMatched hDiscr)

/-- Fuel-parametric native `if` skip for a non-selected lowered switch case. -/
theorem exec_if_nativeSwitchGuardedMatch_miss_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! ≠ EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_nativeSwitchGuardedMatch_miss_ok_fuel fuel state codeOverride
        discrName matchedName tag hMatched hDiscr))

@[simp] theorem exec_lowerAssignNative_lit_ok
    (fuel' : Nat)
    (name : EvmYul.Identifier)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State) :
    EvmYul.Yul.exec (Nat.succ fuel')
      (Backends.lowerAssignNative name (.lit value)) codeOverride state =
      .ok (state.insert name (EvmYul.UInt256.ofNat value)) := by
  simp [Backends.lowerAssignNative, Backends.lowerExprNative]

/-- Native `if` execution for the selected lowered switch case, including the
    leading matched-flag assignment inserted by `lowerNativeSwitchBlock`.

This is the selected-case execution boundary the full lowered-switch proof can
reuse: after the guard hits, the selected body runs in the same state except
for `matchedName := 1`. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec 7 (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .ok final := by
  apply exec_if_nativeSwitchGuardedMatch_hit
      (body := Backends.lowerAssignNative matchedName (.lit 1) :: body)
      (codeOverride := codeOverride) (state := state) (final := final)
      (discrName := discrName) (matchedName := matchedName) (tag := tag)
      hMatched hDiscr
  exact exec_block_cons_ok 7 (Backends.lowerAssignNative matchedName (.lit 1))
    body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
    final (by simp) hBody

/-- Fuel-parametric selected-case guard reduction. -/
theorem eval_nativeSwitchGuardedMatch_hit_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag) :
    EvmYul.Yul.eval (fuel + 8)
      (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
        [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName],
         Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
          [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchGuardedMatch_ok_fuel, hMatched, hDiscr]
  simp [EvmYul.UInt256.eq, EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric selected-case execution, including the matched-flag
    assignment inserted at the start of each lowered native switch case. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .ok final) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .ok final := by
  apply exec_if_eval_nonzero (fuel + 8) _ _ codeOverride state state final
      (EvmYul.UInt256.ofNat 1)
  · exact eval_nativeSwitchGuardedMatch_hit_ok_fuel fuel state codeOverride discrName matchedName tag
      hMatched hDiscr
  · decide
  · exact exec_block_cons_ok (fuel + 7) (Backends.lowerAssignNative matchedName (.lit 1))
      body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
      final (by simp) hBody

/-- Fuel-parametric selected-case execution, including the matched-flag
    assignment inserted at the start of each lowered native switch case, when
    the selected body halts or errors. -/
theorem exec_if_nativeSwitchGuardedMatch_hit_marked_error_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hDiscr : state[discrName]! = EvmYul.UInt256.ofNat tag)
    (hBody :
      EvmYul.Yul.exec (fuel + 7) (.Block body) codeOverride
        (state.insert matchedName (EvmYul.UInt256.ofNat 1)) = .error err) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        (Backends.lowerAssignNative matchedName (.lit 1) :: body))
      codeOverride state = .error err := by
  apply exec_if_eval_nonzero_error (fuel + 8) _ _ codeOverride state state
      (EvmYul.UInt256.ofNat 1) err
  · exact eval_nativeSwitchGuardedMatch_hit_ok_fuel fuel state codeOverride discrName matchedName tag
      hMatched hDiscr
  · decide
  · exact exec_block_cons_tail_error (fuel + 7)
      (Backends.lowerAssignNative matchedName (.lit 1))
      body codeOverride state (state.insert matchedName (EvmYul.UInt256.ofNat 1))
      err (by simp) hBody

/-- Native `if` execution skips a later lowered switch case after an earlier case
    has set the matched flag. -/
theorem exec_if_nativeSwitchGuardedMatch_matched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 9
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  exact exec_if_eval_zero 8 _ body codeOverride state state
    (eval_nativeSwitchGuardedMatch_matched_ok state codeOverride discrName matchedName tag
      hMatched)

/-- Fuel-parametric native `if` skip for a later lowered switch case after an
    earlier case has set the matched flag. -/
theorem exec_if_nativeSwitchGuardedMatch_matched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 9)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
          [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
            [.Var matchedName],
           Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
            [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 8) _ body codeOverride state state
      (eval_nativeSwitchGuardedMatch_matched_ok_fuel fuel state codeOverride
        discrName matchedName tag hMatched))

theorem eval_nativeSwitchDefaultGuard_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.isZero state[matchedName]!) := by
  simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
    EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
    EvmYul.Yul.cons', EvmYul.Yul.head']
  rfl

/-- Fuel-parametric form of `eval_nativeSwitchDefaultGuard_ok`, for use under
    recursively executed generated switch blocks. -/
theorem eval_nativeSwitchDefaultGuard_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.isZero state[matchedName]!) := by
  cases fuel <;>
    simp [Backends.nativePrimCall, EvmYul.Yul.eval, EvmYul.Yul.evalArgs,
      EvmYul.Yul.evalTail, EvmYul.Yul.evalPrimCall, EvmYul.Yul.reverse',
      EvmYul.Yul.cons', EvmYul.Yul.head'] <;> rfl

/-- If no lowered switch case has matched, the default guard is nonzero. -/
theorem eval_nativeSwitchDefaultGuard_unmatched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchDefaultGuard_ok, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric default guard reduction when no case has matched. -/
theorem eval_nativeSwitchDefaultGuard_unmatched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 1) := by
  rw [eval_nativeSwitchDefaultGuard_ok_fuel, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- If a lowered switch case has matched, the default guard is zero. -/
theorem eval_nativeSwitchDefaultGuard_matched_ok
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval 6
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchDefaultGuard_ok, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Fuel-parametric default guard reduction after a case has matched. -/
theorem eval_nativeSwitchDefaultGuard_matched_ok_fuel
    (fuel : Nat)
    (state : EvmYul.Yul.State)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.eval (fuel + 6)
      (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
        [.Var matchedName])
      codeOverride state =
    .ok (state, EvmYul.UInt256.ofNat 0) := by
  rw [eval_nativeSwitchDefaultGuard_ok_fuel, hMatched]
  simp [EvmYul.UInt256.isZero]
  decide

/-- Native `if` execution for the lowered switch default when no case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec 6 (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec 7
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok final := by
  exact exec_if_eval_nonzero 6 _ body codeOverride state state final
    (EvmYul.UInt256.ofNat 1)
    (eval_nativeSwitchDefaultGuard_unmatched_ok state codeOverride matchedName hMatched)
    (by decide)
    hBody

/-- Fuel-parametric default execution when no lowered switch case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec (fuel + 6) (.Block body) codeOverride state = .ok final) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok final := by
  simpa using
    (exec_if_eval_nonzero (fuel + 6) _ body codeOverride state state final
      (EvmYul.UInt256.ofNat 1)
      (eval_nativeSwitchDefaultGuard_unmatched_ok_fuel fuel state codeOverride
        matchedName hMatched)
      (by decide)
      hBody)

/-- Fuel-parametric default execution when no lowered switch case matched and
    the default body halts or errors. -/
theorem exec_if_nativeSwitchDefaultGuard_unmatched_error_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (err : EvmYul.Yul.Exception)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 0)
    (hBody : EvmYul.Yul.exec (fuel + 6) (.Block body) codeOverride state =
      .error err) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .error err := by
  simpa using
    (exec_if_eval_nonzero_error (fuel + 6) _ body codeOverride state state
      (EvmYul.UInt256.ofNat 1) err
      (eval_nativeSwitchDefaultGuard_unmatched_ok_fuel fuel state codeOverride
        matchedName hMatched)
      (by decide)
      hBody)

/-- Native `if` execution skips the lowered switch default after a case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_matched
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec 7
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok state := by
  exact exec_if_eval_zero 6 _ body codeOverride state state
    (eval_nativeSwitchDefaultGuard_matched_ok state codeOverride matchedName hMatched)

/-- Fuel-parametric default skip after a lowered switch case matched. -/
theorem exec_if_nativeSwitchDefaultGuard_matched_fuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state : EvmYul.Yul.State)
    (matchedName : EvmYul.Identifier)
    (hMatched : state[matchedName]! = EvmYul.UInt256.ofNat 1) :
    EvmYul.Yul.exec (fuel + 7)
      (.If
        (Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
          [.Var matchedName])
        body)
      codeOverride state = .ok state := by
  simpa using
    (exec_if_eval_zero (fuel + 6) _ body codeOverride state state
      (eval_nativeSwitchDefaultGuard_matched_ok_fuel fuel state codeOverride
        matchedName hMatched))

def nativeSwitchGuardedMatchExpr
    (discrName matchedName : EvmYul.Identifier)
    (tag : Nat) :
    EvmYul.Yul.Ast.Expr :=
  Backends.nativePrimCall (EvmYul.Operation.AND : EvmYul.Operation .Yul)
    [Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
      [.Var matchedName],
     Backends.nativePrimCall (EvmYul.Operation.EQ : EvmYul.Operation .Yul)
      [.Var discrName, .Lit (EvmYul.UInt256.ofNat tag)]]

def nativeSwitchDefaultGuardExpr
    (matchedName : EvmYul.Identifier) :
    EvmYul.Yul.Ast.Expr :=
  Backends.nativePrimCall (EvmYul.Operation.ISZERO : EvmYul.Operation .Yul)
    [.Var matchedName]

def nativeSwitchCaseIf
    (discrName matchedName : EvmYul.Identifier)
    (entry : Nat × List EvmYul.Yul.Ast.Stmt) :
    EvmYul.Yul.Ast.Stmt :=
  .If (nativeSwitchGuardedMatchExpr discrName matchedName entry.1)
    (Backends.lowerAssignNative matchedName (.lit 1) :: entry.2)

def nativeSwitchCaseIfs
    (discrName matchedName : EvmYul.Identifier)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt)) :
    List EvmYul.Yul.Ast.Stmt :=
  cases.map (nativeSwitchCaseIf discrName matchedName)

def nativeSwitchDefaultIf
    (matchedName : EvmYul.Identifier)
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    List EvmYul.Yul.Ast.Stmt :=
  if defaultBody.isEmpty then []
  else [.If (nativeSwitchDefaultGuardExpr matchedName) defaultBody]

def nativeSwitchTailStmts
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    List EvmYul.Yul.Ast.Stmt :=
  nativeSwitchCaseIfs (Backends.nativeSwitchDiscrTempName switchId)
    (Backends.nativeSwitchMatchedTempName switchId) cases ++
    nativeSwitchDefaultIf (Backends.nativeSwitchMatchedTempName switchId)
      defaultBody

theorem lowerNativeSwitchBlock_selectorExpr_eq_nativeSwitchParts
    (switchId : Nat)
    (cases : List (Nat × List EvmYul.Yul.Ast.Stmt))
    (defaultBody : List EvmYul.Yul.Ast.Stmt) :
    Backends.lowerNativeSwitchBlock Compiler.Proofs.YulGeneration.selectorExpr
      switchId cases defaultBody =
    .Block
      (nativeSwitchPrefixStmts (Backends.nativeSwitchDiscrTempName switchId)
          (Backends.nativeSwitchMatchedTempName switchId) ++
        nativeSwitchTailStmts switchId cases defaultBody) := by
  simp [Backends.lowerNativeSwitchBlock, nativeSwitchPrefixStmts,
    nativeSwitchCaseIfs, nativeSwitchCaseIf, nativeSwitchGuardedMatchExpr,
    nativeSwitchTailStmts, nativeSwitchDefaultIf, nativeSwitchDefaultGuardExpr]

def NativeBlockPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state[name]! = value →
      EvmYul.Yul.exec fuel (.Block body) codeOverride state = .ok final →
        final[name]! = value

def NativeStmtPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state[name]! = value →
      EvmYul.Yul.exec fuel stmt codeOverride state = .ok final →
        final[name]! = value

/-! ## reviveJump simp lemmas

These helpers project `Yul.State` through `reviveJump` which sends Checkpoint
variants back to their inner store via `revive`. They support the new
`_revived` preservation predicates used by Leave-ending body bridges (E2/E4
in `EndToEnd.lean`). -/

@[simp] theorem reviveJump_Ok_eq
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore) :
    (EvmYul.Yul.State.Ok shared store).reviveJump =
      EvmYul.Yul.State.Ok shared store := rfl

@[simp] theorem reviveJump_OutOfFuel_eq :
    EvmYul.Yul.State.OutOfFuel.reviveJump = EvmYul.Yul.State.OutOfFuel := rfl

@[simp] theorem reviveJump_Leave_eq
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore) :
    (EvmYul.Yul.State.Checkpoint (.Leave shared store)).reviveJump =
      EvmYul.Yul.State.Ok shared store := rfl

@[simp] theorem reviveJump_Continue_eq
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore) :
    (EvmYul.Yul.State.Checkpoint (.Continue shared store)).reviveJump =
      EvmYul.Yul.State.Ok shared store := rfl

@[simp] theorem reviveJump_Break_eq
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore) :
    (EvmYul.Yul.State.Checkpoint (.Break shared store)).reviveJump =
      EvmYul.Yul.State.Ok shared store := rfl

theorem reviveJump_eq_ok_ne_outOfFuel
    (final : EvmYul.Yul.State)
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore)
    (hRevive : final.reviveJump = EvmYul.Yul.State.Ok shared store) :
    final ≠ EvmYul.Yul.State.OutOfFuel := by
  intro hFinal
  subst hFinal
  simp [EvmYul.Yul.State.reviveJump] at hRevive

/-- A selected body that projects through `reviveJump` to an `Ok` endpoint
    cannot have produced the raw `.OutOfFuel` state. This keeps the checkpoint
    dispatcher stack from considering the impossible out-of-fuel endpoint when
    a selected case body returned `.ok final`. -/
theorem selected_body_ok_reviveJump_ne_outOfFuel
    (fuel : Nat)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (state final : EvmYul.Yul.State)
    (shared : EvmYul.SharedState EvmYul.OperationType.Yul)
    (store : EvmYul.Yul.VarStore)
    (_hBody :
      EvmYul.Yul.exec fuel (.Block body) codeOverride state = .ok final)
    (hRevive : final.reviveJump = EvmYul.Yul.State.Ok shared store) :
    final ≠ EvmYul.Yul.State.OutOfFuel :=
  reviveJump_eq_ok_ne_outOfFuel final shared store hRevive

/-! ## NativeBlockPreservesWord_revived

Parallel preservation predicate that reads the revived store on both the
hypothesis and the conclusion. This is the form that handles Leave-ending
bodies: `final = Checkpoint (.Leave shared store)` has `final.reviveJump =
Ok shared store`, so the lookup reads the inner store rather than falling
through to ⟨0⟩ via the empty `default` Finmap. -/

def NativeBlockPreservesWord_revived
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (body : List EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state.reviveJump[name]! = value →
      EvmYul.Yul.exec fuel (.Block body) codeOverride state = .ok final →
        final.reviveJump[name]! = value

def NativeStmtPreservesWord_revived
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (stmt : EvmYul.Yul.Ast.Stmt)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final,
    state.reviveJump[name]! = value →
      EvmYul.Yul.exec fuel stmt codeOverride state = .ok final →
        final.reviveJump[name]! = value

def NativeExprPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (expr : EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final result,
    state[name]! = value →
      EvmYul.Yul.eval fuel expr codeOverride state = .ok (final, result) →
        final[name]! = value

def NativeEvalArgsPreservesWord
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) : Prop :=
  ∀ fuel state final results,
    state[name]! = value →
      EvmYul.Yul.evalArgs fuel args codeOverride state = .ok (final, results) →
        final[name]! = value

theorem state_lookup_insert_of_ne
    (state : EvmYul.Yul.State)
    (name other : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (hne : name ≠ other) :
    EvmYul.Yul.State.lookup! name (state.insert other value) =
      EvmYul.Yul.State.lookup! name state := by
  cases state with
  | Ok shared store =>
      simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!]
      rw [Finmap.lookup_insert_of_ne store hne]
  | OutOfFuel => simp [EvmYul.Yul.State.insert]
  | Checkpoint jump => simp [EvmYul.Yul.State.insert]

theorem state_getElem_insert_of_ne
    (state : EvmYul.Yul.State)
    (name other : EvmYul.Identifier)
    (value : EvmYul.Literal)
    (hne : name ≠ other) :
    (state.insert other value)[name]! = state[name]! := by
  cases state with
  | Ok shared store =>
      simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!,
        EvmYul.Yul.State.store, GetElem?.getElem!, decidableGetElem?,
        GetElem.getElem]
      by_cases hmem : name ∈ store
      · simp [hmem, hne, Finmap.lookup_insert_of_ne store hne]
      · simp [hmem, hne]
  | OutOfFuel =>
      simp [EvmYul.Yul.State.insert]
  | Checkpoint jump =>
      simp [EvmYul.Yul.State.insert]

theorem state_getElem_insert_self_ok
    (shared : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier)
    (value : EvmYul.Literal) :
    (((EvmYul.Yul.State.Ok shared store : EvmYul.Yul.State).insert
      name value)[name]!) = value := by
  simp [EvmYul.Yul.State.insert, EvmYul.Yul.State.lookup!,
    EvmYul.Yul.State.store, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem]

theorem state_getElem_multifill_of_not_mem
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (vars : List EvmYul.Identifier)
    (vals : List EvmYul.Literal)
    (hnot : name ∉ vars) :
    (EvmYul.Yul.State.multifill vars vals state)[name]! = state[name]! := by
  induction vars generalizing state vals with
  | nil =>
      cases state <;> simp [EvmYul.Yul.State.multifill]
  | cons var rest ih =>
      simp at hnot
      rcases hnot with ⟨hneq, hrest⟩
      cases vals with
      | nil =>
          cases state <;> simp [EvmYul.Yul.State.multifill]
      | cons val restVals =>
          cases state with
          | Ok shared store =>
              have hTail :
                  (EvmYul.Yul.State.multifill rest restVals
                    (EvmYul.Yul.State.Ok shared store))[name]! =
                    (EvmYul.Yul.State.Ok shared store)[name]! :=
                ih (EvmYul.Yul.State.Ok shared store) restVals hrest
              simp [EvmYul.Yul.State.multifill]
              rw [state_getElem_insert_of_ne
                (List.foldr (fun x s => s.insert x.1 x.2)
                  (EvmYul.Yul.State.Ok shared store) (rest.zip restVals))
                name var val hneq]
              simpa [EvmYul.Yul.State.multifill] using hTail
          | OutOfFuel =>
              rfl
          | Checkpoint jump =>
              rfl

theorem state_getElem_foldr_insert_zero_of_not_mem
    (state : EvmYul.Yul.State)
    (name : EvmYul.Identifier)
    (vars : List EvmYul.Identifier)
    (hnot : name ∉ vars) :
    ((List.foldr (fun var s => s.insert var ⟨0⟩) state vars))[name]! =
      state[name]! := by
  induction vars generalizing state with
  | nil =>
      rfl
  | cons var rest ih =>
      simp at hnot
      rcases hnot with ⟨hneq, hrest⟩
      have hTail :
          (List.foldr (fun var s => s.insert var ⟨0⟩) state rest)[name]! =
            state[name]! :=
        ih state hrest
      change
        ((List.foldr (fun var s => s.insert var ⟨0⟩) state rest).insert
          var ⟨0⟩)[name]! = state[name]!
      rw [state_getElem_insert_of_ne
        (List.foldr (fun var s => s.insert var ⟨0⟩) state rest)
        name var ⟨0⟩ hneq, hTail]

theorem state_getElem_setSharedState
    (state : EvmYul.Yul.State)
    (shared : EvmYul.SharedState .Yul)
    (name : EvmYul.Identifier) :
    (state.setSharedState shared)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setMachineState
    (state : EvmYul.Yul.State)
    (mstate : EvmYul.MachineState)
    (name : EvmYul.Identifier) :
    (state.setMachineState mstate)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setState
    (state : EvmYul.Yul.State)
    (estate : EvmYul.State .Yul)
    (name : EvmYul.Identifier) :
    (state.setState estate)[name]! = state[name]! := by
  cases state <;> rfl

theorem state_getElem_setStore_ok_left
    (shared : EvmYul.SharedState .Yul)
    (shared' : EvmYul.SharedState .Yul)
    (store : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) :
    (((EvmYul.Yul.State.Ok shared ∅) : EvmYul.Yul.State).setStore
      (EvmYul.Yul.State.Ok shared' store))[name]! =
      (EvmYul.Yul.State.Ok shared' store)[name]! := by
  simp [EvmYul.Yul.State.setStore, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem state_getElem_setStore_ok
    (shared shared' : EvmYul.SharedState .Yul)
    (store store' : EvmYul.Yul.VarStore)
    (name : EvmYul.Identifier) :
    (((EvmYul.Yul.State.Ok shared store) : EvmYul.Yul.State).setStore
      (EvmYul.Yul.State.Ok shared' store'))[name]! =
      (EvmYul.Yul.State.Ok shared' store')[name]! := by
  simp [EvmYul.Yul.State.setStore, GetElem?.getElem!, decidableGetElem?,
    GetElem.getElem, EvmYul.Yul.State.store, EvmYul.Yul.State.lookup!]

theorem NativePrimCallPreservesWord_calldatasize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATASIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_calldatasize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_calldatasize_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATASIZE values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_calldatasize name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_calldatasize_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_callvalue
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLVALUE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_callvalue_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_callvalue_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLVALUE values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_callvalue name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_callvalue_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_address
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDRESS [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_address_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_address_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDRESS values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_address name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_address_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_balance
    (name : EvmYul.Identifier)
    (expected account : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BALANCE [account] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_balance_ok] at hExec
      cases hExec
      cases state with
      | Ok shared store =>
          change ((EvmYul.Yul.State.Ok shared store).setSharedState _)[name]! = expected
          rw [state_getElem_setSharedState]
          exact hLookup
      | OutOfFuel =>
          change ((EvmYul.Yul.State.OutOfFuel).setSharedState _)[name]! = expected
          rw [state_getElem_setSharedState]
          exact hLookup
      | Checkpoint jump =>
          cases jump <;>
            convert hLookup using 1 <;> simp [EvmYul.Yul.State.setSharedState]

theorem NativePrimCallPreservesWord_origin
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ORIGIN [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_origin_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_origin_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ORIGIN values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_origin_any_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_caller
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLER [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_caller_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_caller_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLER values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_caller name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_caller_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_timestamp
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TIMESTAMP [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_timestamp_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_timestamp_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TIMESTAMP values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_timestamp name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_timestamp_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_number
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NUMBER [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_number_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_number_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NUMBER values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_number name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_number_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_chainid
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CHAINID [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_chainid_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_chainid_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CHAINID values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_chainid name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_chainid_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_blobbasefee
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BLOBBASEFEE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_blobbasefee_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_blobbasefee_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BLOBBASEFEE values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      exact NativePrimCallPreservesWord_blobbasefee name expected
        fuel state final rets hLookup hExec
  | cons value rest =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [primCall_blobbasefee_any_ok] at hExec
          cases hExec
          exact hLookup

theorem NativePrimCallPreservesWord_gasprice
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GASPRICE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gasprice_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_coinbase
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.COINBASE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_coinbase_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_gaslimit
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GASLIMIT [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gaslimit_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_selfbalance
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SELFBALANCE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_selfbalance_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_unary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected value result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [value] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [value] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_unary_same_state_values
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (hNil :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hOverarity :
      ∀ fuel state value extra rest,
        EvmYul.Yul.primCall (fuel + 1) state op
          (value :: extra :: rest) =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hPrecise :
      ∀ value,
        ∀ fuel state final rets,
          state[name]! = expected →
            EvmYul.Yul.primCall fuel state op [value] =
              .ok (final, rets) →
            final[name]! = expected) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [hNil fuel' state] at hExec
          simp at hExec
  | cons value rest =>
      cases rest with
      | nil =>
          exact hPrecise value fuel state final rets hLookup hExec
      | cons extra tail =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              rw [hOverarity fuel' state value extra tail] at hExec
              simp at hExec

theorem NativePrimCallPreservesWord_binary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected left right result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [left, right] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [left, right] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_ternary_same_state
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected first second third result : EvmYul.Literal)
    (hStep :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [first, second, third] =
          .ok (state, [result])) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op [first, second, third] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [hStep fuel' state] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_binary_same_state_values
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (hNil :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hSingleton :
      ∀ fuel state left,
        EvmYul.Yul.primCall (fuel + 1) state op [left] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hOverarity :
      ∀ fuel state left right extra rest,
        EvmYul.Yul.primCall (fuel + 1) state op
          (left :: right :: extra :: rest) =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hPrecise :
      ∀ left right,
        ∀ fuel state final rets,
          state[name]! = expected →
            EvmYul.Yul.primCall fuel state op [left, right] =
              .ok (final, rets) →
            final[name]! = expected) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [hNil fuel' state] at hExec
          simp at hExec
  | cons left rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              rw [hSingleton fuel' state left] at hExec
              simp at hExec
      | cons right rest =>
          cases rest with
          | nil =>
              exact hPrecise left right fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero =>
                  simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  rw [hOverarity fuel' state left right extra tail] at hExec
                  simp at hExec

theorem NativePrimCallPreservesWord_ternary_same_state_values
    (op : EvmYul.Operation .Yul)
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (hNil :
      ∀ fuel state,
        EvmYul.Yul.primCall (fuel + 1) state op [] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hSingleton :
      ∀ fuel state first,
        EvmYul.Yul.primCall (fuel + 1) state op [first] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hPair :
      ∀ fuel state first second,
        EvmYul.Yul.primCall (fuel + 1) state op [first, second] =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hOverarity :
      ∀ fuel state first second third extra rest,
        EvmYul.Yul.primCall (fuel + 1) state op
          (first :: second :: third :: extra :: rest) =
          Except.error EvmYul.Yul.Exception.InvalidArguments)
    (hPrecise :
      ∀ first second third,
        ∀ fuel state final rets,
          state[name]! = expected →
            EvmYul.Yul.primCall fuel state op [first, second, third] =
              .ok (final, rets) →
            final[name]! = expected) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          rw [hNil fuel' state] at hExec
          simp at hExec
  | cons first rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              rw [hSingleton fuel' state first] at hExec
              simp at hExec
      | cons second rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero =>
                  simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  rw [hPair fuel' state first second] at hExec
                  simp at hExec
          | cons third rest =>
              cases rest with
              | nil =>
                  exact hPrecise first second third fuel state final rets
                    hLookup hExec
              | cons extra tail =>
                  cases fuel with
                  | zero =>
                      simp [EvmYul.Yul.primCall] at hExec
                  | succ fuel' =>
                      rw [hOverarity fuel' state first second third extra tail]
                        at hExec
                      simp at hExec

theorem NativePrimCallPreservesWord_iszero
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ISZERO [value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state EvmYul.Operation.ISZERO
    name expected value (EvmYul.UInt256.isZero value)
    (by intro fuel state; exact primCall_iszero_ok fuel state value)

theorem NativePrimCallPreservesWord_iszero_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ISZERO values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values EvmYul.Operation.ISZERO
    name expected primCall_iszero_nil_invalid
    primCall_iszero_overarity_invalid
    (fun value => NativePrimCallPreservesWord_iszero name expected value)

theorem NativePrimCallPreservesWord_shr
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHR [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SHR
    name expected shift value (EvmYul.UInt256.shiftRight value shift)
    (by intro fuel state; exact primCall_shr_ok fuel state shift value)

theorem NativePrimCallPreservesWord_shr_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHR values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SHR
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shr_nil_invalid])
    (by intro fuel state shift; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shr_singleton_invalid])
    (by intro fuel state shift value extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shr_overarity_invalid])
    (fun shift value => NativePrimCallPreservesWord_shr name expected shift value)

theorem NativePrimCallPreservesWord_add
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.ADD
    name expected left right (EvmYul.UInt256.add left right)
    (by intro fuel state; exact primCall_add_ok fuel state left right)

theorem NativePrimCallPreservesWord_add_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADD values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          simp only [EvmYul.Yul.primCall] at hExec
          rw [step_add_nil_invalid] at hExec
          simp at hExec
  | cons left rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              simp only [EvmYul.Yul.primCall] at hExec
              rw [step_add_singleton_invalid] at hExec
              simp at hExec
      | cons right rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_add name expected left right
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero =>
                  simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  simp only [EvmYul.Yul.primCall] at hExec
                  rw [step_add_overarity_invalid] at hExec
                  simp at hExec

theorem NativePrimCallPreservesWord_sub
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SUB [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SUB
    name expected left right (EvmYul.UInt256.sub left right)
    (by intro fuel state; exact primCall_sub_ok fuel state left right)

theorem NativePrimCallPreservesWord_sub_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SUB values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          simp only [EvmYul.Yul.primCall] at hExec
          rw [step_sub_nil_invalid] at hExec
          simp at hExec
  | cons left rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              simp only [EvmYul.Yul.primCall] at hExec
              rw [step_sub_singleton_invalid] at hExec
              simp at hExec
      | cons right rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_sub name expected left right
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero =>
                  simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  simp only [EvmYul.Yul.primCall] at hExec
                  rw [step_sub_overarity_invalid] at hExec
                  simp at hExec

theorem NativePrimCallPreservesWord_mul
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MUL [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.MUL
    name expected left right (EvmYul.UInt256.mul left right)
    (by intro fuel state; exact primCall_mul_ok fuel state left right)

theorem NativePrimCallPreservesWord_mul_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MUL values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero =>
          simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          simp only [EvmYul.Yul.primCall] at hExec
          rw [step_mul_nil_invalid] at hExec
          simp at hExec
  | cons left rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero =>
              simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              simp only [EvmYul.Yul.primCall] at hExec
              rw [step_mul_singleton_invalid] at hExec
              simp at hExec
      | cons right rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_mul name expected left right
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero =>
                  simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  simp only [EvmYul.Yul.primCall] at hExec
                  rw [step_mul_overarity_invalid] at hExec
                  simp at hExec

theorem NativePrimCallPreservesWord_div
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.DIV [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.DIV
    name expected left right (EvmYul.UInt256.div left right)
    (by intro fuel state; exact primCall_div_ok fuel state left right)

theorem NativePrimCallPreservesWord_div_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.DIV values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.DIV
    name expected primCall_div_nil_invalid primCall_div_singleton_invalid
    primCall_div_overarity_invalid
    (fun left right => NativePrimCallPreservesWord_div name expected left right)

theorem NativePrimCallPreservesWord_mod
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MOD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.MOD
    name expected left right (EvmYul.UInt256.mod left right)
    (by intro fuel state; exact primCall_mod_ok fuel state left right)

theorem NativePrimCallPreservesWord_mod_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MOD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.MOD
    name expected primCall_mod_nil_invalid primCall_mod_singleton_invalid
    primCall_mod_overarity_invalid
    (fun left right => NativePrimCallPreservesWord_mod name expected left right)

theorem NativePrimCallPreservesWord_sdiv
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SDIV [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SDIV
    name expected left right (EvmYul.UInt256.sdiv left right)
    (by intro fuel state; exact primCall_sdiv_ok fuel state left right)

theorem NativePrimCallPreservesWord_sdiv_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SDIV values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SDIV
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sdiv_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sdiv_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sdiv_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_sdiv name expected left right)

theorem NativePrimCallPreservesWord_smod
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SMOD [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SMOD
    name expected left right (EvmYul.UInt256.smod left right)
    (by intro fuel state; exact primCall_smod_ok fuel state left right)

theorem NativePrimCallPreservesWord_smod_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SMOD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SMOD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_smod_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_smod_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_smod_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_smod name expected left right)

theorem NativePrimCallPreservesWord_addmod
    (name : EvmYul.Identifier)
    (expected left right modulus : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDMOD
          [left, right, modulus] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state EvmYul.Operation.ADDMOD
    name expected left right modulus
    (EvmYul.UInt256.addMod left right modulus)
    (by intro fuel state; exact primCall_addmod_ok fuel state left right modulus)

theorem NativePrimCallPreservesWord_addmod_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.ADDMOD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state_values EvmYul.Operation.ADDMOD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_addmod_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_addmod_singleton_invalid])
    (by intro fuel state left right; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_addmod_pair_invalid])
    (by intro fuel state left right modulus extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_addmod_overarity_invalid])
    (fun left right modulus =>
      NativePrimCallPreservesWord_addmod name expected left right modulus)

theorem NativePrimCallPreservesWord_mulmod
    (name : EvmYul.Identifier)
    (expected left right modulus : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MULMOD
          [left, right, modulus] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state EvmYul.Operation.MULMOD
    name expected left right modulus
    (EvmYul.UInt256.mulMod left right modulus)
    (by intro fuel state; exact primCall_mulmod_ok fuel state left right modulus)

theorem NativePrimCallPreservesWord_mulmod_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MULMOD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state_values EvmYul.Operation.MULMOD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mulmod_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mulmod_singleton_invalid])
    (by intro fuel state left right; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mulmod_pair_invalid])
    (by intro fuel state left right modulus extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mulmod_overarity_invalid])
    (fun left right modulus =>
      NativePrimCallPreservesWord_mulmod name expected left right modulus)

theorem NativePrimCallPreservesWord_exp
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EXP [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.EXP
    name expected left right (EvmYul.UInt256.exp left right)
    (by intro fuel state; exact primCall_exp_ok fuel state left right)

theorem NativePrimCallPreservesWord_exp_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EXP values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.EXP
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_exp_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_exp_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_exp_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_exp name expected left right)

theorem NativePrimCallPreservesWord_signextend
    (name : EvmYul.Identifier)
    (expected byteIdx value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SIGNEXTEND
          [byteIdx, value] = .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SIGNEXTEND
    name expected byteIdx value (EvmYul.UInt256.signextend byteIdx value)
    (by intro fuel state; exact primCall_signextend_ok fuel state byteIdx value)

theorem NativePrimCallPreservesWord_signextend_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SIGNEXTEND values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values
    EvmYul.Operation.SIGNEXTEND name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_signextend_nil_invalid])
    (by intro fuel state byteIdx; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_signextend_singleton_invalid])
    (by intro fuel state byteIdx value extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_signextend_overarity_invalid])
    (fun byteIdx value =>
      NativePrimCallPreservesWord_signextend name expected byteIdx value)

theorem NativePrimCallPreservesWord_eq
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EQ [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.EQ
    name expected left right (EvmYul.UInt256.eq left right)
    (by intro fuel state; exact primCall_eq_ok fuel state left right)

theorem NativePrimCallPreservesWord_eq_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.EQ values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.EQ
    name expected primCall_eq_nil_invalid primCall_eq_singleton_invalid
    primCall_eq_overarity_invalid
    (fun left right => NativePrimCallPreservesWord_eq name expected left right)

theorem NativePrimCallPreservesWord_lt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.LT
    name expected left right (EvmYul.UInt256.lt left right)
    (by intro fuel state; exact primCall_lt_ok fuel state left right)

theorem NativePrimCallPreservesWord_lt_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LT values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.LT
    name expected primCall_lt_nil_invalid primCall_lt_singleton_invalid
    primCall_lt_overarity_invalid
    (fun left right => NativePrimCallPreservesWord_lt name expected left right)

theorem NativePrimCallPreservesWord_gt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.GT
    name expected left right (EvmYul.UInt256.gt left right)
    (by intro fuel state; exact primCall_gt_ok fuel state left right)

theorem NativePrimCallPreservesWord_gt_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GT values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.GT
    name expected primCall_gt_nil_invalid primCall_gt_singleton_invalid
    primCall_gt_overarity_invalid
    (fun left right => NativePrimCallPreservesWord_gt name expected left right)

theorem NativePrimCallPreservesWord_slt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SLT
    name expected left right (EvmYul.UInt256.slt left right)
    (by intro fuel state; exact primCall_slt_ok fuel state left right)

theorem NativePrimCallPreservesWord_slt_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLT values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SLT
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_slt_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_slt_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_slt_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_slt name expected left right)

theorem NativePrimCallPreservesWord_sgt
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SGT [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SGT
    name expected left right (EvmYul.UInt256.sgt left right)
    (by intro fuel state; exact primCall_sgt_ok fuel state left right)

theorem NativePrimCallPreservesWord_sgt_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SGT values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SGT
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sgt_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sgt_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sgt_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_sgt name expected left right)

theorem NativePrimCallPreservesWord_and
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.AND [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.AND
    name expected left right (EvmYul.UInt256.land left right)
    (by intro fuel state; exact primCall_and_ok fuel state left right)

theorem NativePrimCallPreservesWord_and_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.AND values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.AND
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_and_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_and_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_and_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_and name expected left right)

theorem NativePrimCallPreservesWord_or
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.OR [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.OR
    name expected left right (EvmYul.UInt256.lor left right)
    (by intro fuel state; exact primCall_or_ok fuel state left right)

theorem NativePrimCallPreservesWord_or_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.OR values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.OR
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_or_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_or_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_or_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_or name expected left right)

theorem NativePrimCallPreservesWord_xor
    (name : EvmYul.Identifier)
    (expected left right : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.XOR [left, right] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.XOR
    name expected left right (EvmYul.UInt256.xor left right)
    (by intro fuel state; exact primCall_xor_ok fuel state left right)

theorem NativePrimCallPreservesWord_xor_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.XOR values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.XOR
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_xor_nil_invalid])
    (by intro fuel state left; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_xor_singleton_invalid])
    (by intro fuel state left right extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_xor_overarity_invalid])
    (fun left right => NativePrimCallPreservesWord_xor name expected left right)

theorem NativePrimCallPreservesWord_not
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NOT [value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state EvmYul.Operation.NOT
    name expected value (EvmYul.UInt256.lnot value)
    (by intro fuel state; exact primCall_not_ok fuel state value)

theorem NativePrimCallPreservesWord_not_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.NOT values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values EvmYul.Operation.NOT
    name expected primCall_not_nil_invalid primCall_not_overarity_invalid
    (fun value => NativePrimCallPreservesWord_not name expected value)

theorem NativePrimCallPreservesWord_shl
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHL [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SHL
    name expected shift value (EvmYul.UInt256.shiftLeft value shift)
    (by intro fuel state; exact primCall_shl_ok fuel state shift value)

theorem NativePrimCallPreservesWord_shl_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SHL values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SHL
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shl_nil_invalid])
    (by intro fuel state shift; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shl_singleton_invalid])
    (by intro fuel state shift value extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_shl_overarity_invalid])
    (fun shift value => NativePrimCallPreservesWord_shl name expected shift value)

theorem NativePrimCallPreservesWord_byte
    (name : EvmYul.Identifier)
    (expected index value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BYTE [index, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.BYTE
    name expected index value (EvmYul.UInt256.byteAt index value)
    (by intro fuel state; exact primCall_byte_ok fuel state index value)

theorem NativePrimCallPreservesWord_byte_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.BYTE values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.BYTE
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_byte_nil_invalid])
    (by intro fuel state index; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_byte_singleton_invalid])
    (by intro fuel state index value extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_byte_overarity_invalid])
    (fun index value => NativePrimCallPreservesWord_byte name expected index value)

theorem NativePrimCallPreservesWord_sar
    (name : EvmYul.Identifier)
    (expected shift value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SAR [shift, value] =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state EvmYul.Operation.SAR
    name expected shift value (EvmYul.UInt256.sar shift value)
    (by intro fuel state; exact primCall_sar_ok fuel state shift value)

theorem NativePrimCallPreservesWord_sar_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SAR values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.SAR
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sar_nil_invalid])
    (by intro fuel state shift; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sar_singleton_invalid])
    (by intro fuel state shift value extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sar_overarity_invalid])
    (fun shift value => NativePrimCallPreservesWord_sar name expected shift value)

theorem NativePrimCallPreservesWord_sload
    (name : EvmYul.Identifier)
    (expected slot : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLOAD [slot] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_sload_ok] at hExec
      cases hSload : state.toState.sload slot with
      | mk state' value =>
          simp [hSload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setSharedState]
          exact hLookup

theorem NativePrimCallPreservesWord_sload_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SLOAD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values EvmYul.Operation.SLOAD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sload_nil_invalid])
    (by intro fuel state slot extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_sload_overarity_invalid])
    (fun slot => NativePrimCallPreservesWord_sload name expected slot)

theorem NativePrimCallPreservesWord_calldataload
    (name : EvmYul.Identifier)
    (expected offset : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATALOAD [offset] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      cases state with
      | Ok shared store =>
          rw [primCall_calldataload_ok] at hExec
          cases hExec
          exact hLookup
      | OutOfFuel =>
          simp [EvmYul.Yul.primCall] at hExec
          cases hExec
          exact hLookup
      | Checkpoint jump =>
          cases jump <;> simp [EvmYul.Yul.primCall] at hExec <;>
            cases hExec <;> exact hLookup

theorem NativePrimCallPreservesWord_calldataload_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATALOAD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values
    EvmYul.Operation.CALLDATALOAD name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_calldataload_nil_invalid])
    (by intro fuel state offset extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_calldataload_overarity_invalid])
    (fun offset => NativePrimCallPreservesWord_calldataload name expected offset)

theorem NativePrimCallPreservesWord_mload
    (name : EvmYul.Identifier)
    (expected offset : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MLOAD [offset] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mload_ok] at hExec
      cases hMload : state.toSharedState.toMachineState.mload offset with
      | mk value machineState' =>
          simp [hMload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setMachineState]
          exact hLookup

theorem NativePrimCallPreservesWord_mload_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MLOAD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values EvmYul.Operation.MLOAD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mload_nil_invalid])
    (by intro fuel state offset extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_mload_overarity_invalid])
    (fun offset => NativePrimCallPreservesWord_mload name expected offset)

theorem NativePrimCallPreservesWord_mstore
    (name : EvmYul.Identifier)
    (expected offset value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE [offset, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mstore_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_mstore_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.MSTORE
    name expected primCall_mstore_nil_invalid
    primCall_mstore_singleton_invalid primCall_mstore_overarity_invalid
    (fun offset value =>
      NativePrimCallPreservesWord_mstore name expected offset value)

theorem NativePrimCallPreservesWord_mstore8
    (name : EvmYul.Identifier)
    (expected offset value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE8 [offset, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_mstore8_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_mstore8_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSTORE8 values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.MSTORE8
    name expected primCall_mstore8_nil_invalid
    primCall_mstore8_singleton_invalid primCall_mstore8_overarity_invalid
    (fun offset value =>
      NativePrimCallPreservesWord_mstore8 name expected offset value)

theorem NativePrimCallPreservesWord_tload
    (name : EvmYul.Identifier)
    (expected slot : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TLOAD [slot] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_tload_ok] at hExec
      cases hTload : state.toState.tload slot with
      | mk state' value =>
          simp [hTload] at hExec
          cases hExec
          subst final
          rw [state_getElem_setSharedState]
          exact hLookup

theorem NativePrimCallPreservesWord_tload_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TLOAD values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_unary_same_state_values EvmYul.Operation.TLOAD
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_tload_nil_invalid])
    (by intro fuel state slot extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_tload_overarity_invalid])
    (fun slot => NativePrimCallPreservesWord_tload name expected slot)

theorem NativePrimCallPreservesWord_tstore
    (name : EvmYul.Identifier)
    (expected slot value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TSTORE [slot, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_tstore_ok fuel' state slot value hPerm] at hExec
        cases hExec
        rw [state_getElem_setState]
        exact hLookup
      · simp [EvmYul.Yul.primCall, hPerm] at hExec
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
              Except EvmYul.Yul.Exception
                (EvmYul.Yul.State × List EvmYul.Literal)) =
            Except.ok (final, rets) at hExec
        cases hExec

theorem NativePrimCallPreservesWord_tstore_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.TSTORE values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm, step_tstore_nil_invalid] at hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            change
              (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                  Except EvmYul.Yul.Exception
                    (EvmYul.Yul.State × List EvmYul.Literal)) =
                Except.ok (final, rets) at hExec
            cases hExec
  | cons slot rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm,
                  step_tstore_singleton_invalid] at hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                change
                  (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                      Except EvmYul.Yul.Exception
                        (EvmYul.Yul.State × List EvmYul.Literal)) =
                    Except.ok (final, rets) at hExec
                cases hExec
      | cons value rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_tstore name expected slot value
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm,
                      step_tstore_overarity_invalid] at hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    change
                      (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                          Except EvmYul.Yul.Exception
                            (EvmYul.Yul.State × List EvmYul.Literal)) =
                        Except.ok (final, rets) at hExec
                    cases hExec

theorem NativePrimCallPreservesWord_sstore
    (name : EvmYul.Identifier)
    (expected slot value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SSTORE [slot, value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_sstore_ok fuel' state slot value hPerm] at hExec
        cases hExec
        rw [state_getElem_setState]
        exact hLookup
      · simp [EvmYul.Yul.primCall, hPerm] at hExec
        change
          (Except.error EvmYul.Yul.Exception.StaticModeViolation :
              Except EvmYul.Yul.Exception
                (EvmYul.Yul.State × List EvmYul.Literal)) =
            Except.ok (final, rets) at hExec
        cases hExec

theorem NativePrimCallPreservesWord_sstore_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.SSTORE values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm, step_sstore_nil_invalid] at hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            change
              (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                  Except EvmYul.Yul.Exception
                    (EvmYul.Yul.State × List EvmYul.Literal)) =
                Except.ok (final, rets) at hExec
            cases hExec
  | cons slot rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm,
                  step_sstore_singleton_invalid] at hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                change
                  (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                      Except EvmYul.Yul.Exception
                        (EvmYul.Yul.State × List EvmYul.Literal)) =
                    Except.ok (final, rets) at hExec
                cases hExec
      | cons value rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_sstore name expected slot value
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm,
                      step_sstore_overarity_invalid] at hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    change
                      (Except.error EvmYul.Yul.Exception.StaticModeViolation :
                          Except EvmYul.Yul.Exception
                            (EvmYul.Yul.State × List EvmYul.Literal)) =
                        Except.ok (final, rets) at hExec
                    cases hExec

theorem NativePrimCallPreservesWord_stop
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.STOP [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_stop_ok] at hExec
      cases hExec

theorem NativePrimCallPreservesWord_return
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURN [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_return_ok fuel' state offset size] at hExec
      cases hReturn :
          EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmReturn
            state [offset, size] with
      | error err =>
          simp [hReturn] at hExec
      | ok ret =>
          rcases ret with ⟨returnState, value⟩
          simp [hReturn] at hExec

theorem NativePrimCallPreservesWord_revert
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.REVERT [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets _hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_revert_ok fuel' state offset size] at hExec
      cases hRevert :
          EvmYul.Yul.binaryMachineStateOp EvmYul.MachineState.evmRevert
            state [offset, size] with
      | error err =>
          simp [hRevert] at hExec
      | ok ret =>
          rcases ret with ⟨revertState, value⟩
          simp [hRevert] at hExec

theorem NativePrimCallPreservesWord_return_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURN values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          simp [EvmYul.Yul.primCall, step_return_nil_invalid] at hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              simp [EvmYul.Yul.primCall, step_return_singleton_invalid] at hExec
      | cons size rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_return name expected offset size
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  simp [EvmYul.Yul.primCall, step_return_overarity_invalid] at hExec

theorem NativePrimCallPreservesWord_revert_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.REVERT values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          simp [EvmYul.Yul.primCall, step_revert_nil_invalid] at hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              simp [EvmYul.Yul.primCall, step_revert_singleton_invalid] at hExec
      | cons size rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_revert name expected offset size
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  simp [EvmYul.Yul.primCall, step_revert_overarity_invalid] at hExec

theorem NativePrimCallPreservesWord_msize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.MSIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_msize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_gas
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.GAS [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_gas_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_returndatasize
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURNDATASIZE [] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_returndatasize_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_calldatacopy
    (name : EvmYul.Identifier)
    (expected mstart datastart size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATACOPY
          [mstart, datastart, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_calldatacopy_ok] at hExec
      cases hExec
      rw [state_getElem_setSharedState]
      exact hLookup

theorem NativePrimCallPreservesWord_returndatacopy
    (name : EvmYul.Identifier)
    (expected mstart rstart size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURNDATACOPY
          [mstart, rstart, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_returndatacopy_ok] at hExec
      cases hExec
      rw [state_getElem_setMachineState]
      exact hLookup

theorem NativePrimCallPreservesWord_calldatacopy_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.CALLDATACOPY values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state_values
    EvmYul.Operation.CALLDATACOPY name expected
    (by intro fuel state; simp [EvmYul.Yul.primCall,
      step_calldatacopy_nil_invalid])
    (by intro fuel state mstart; simp [EvmYul.Yul.primCall,
      step_calldatacopy_singleton_invalid])
    (by intro fuel state mstart datastart; simp [EvmYul.Yul.primCall,
      step_calldatacopy_pair_invalid])
    (by
      intro fuel state mstart datastart size extra rest
      simp [EvmYul.Yul.primCall, step_calldatacopy_overarity_invalid])
    (fun mstart datastart size =>
      NativePrimCallPreservesWord_calldatacopy name expected mstart datastart
        size)

theorem NativePrimCallPreservesWord_returndatacopy_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.RETURNDATACOPY values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_ternary_same_state_values
    EvmYul.Operation.RETURNDATACOPY name expected
    (by intro fuel state; simp [EvmYul.Yul.primCall,
      step_returndatacopy_nil_invalid])
    (by intro fuel state mstart; simp [EvmYul.Yul.primCall,
      step_returndatacopy_singleton_invalid])
    (by intro fuel state mstart rstart; simp [EvmYul.Yul.primCall,
      step_returndatacopy_pair_invalid])
    (by
      intro fuel state mstart rstart size extra rest
      simp [EvmYul.Yul.primCall, step_returndatacopy_overarity_invalid])
    (fun mstart rstart size =>
      NativePrimCallPreservesWord_returndatacopy name expected mstart rstart
        size)

theorem NativePrimCallPreservesWord_pop
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.POP [value] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_pop_ok] at hExec
      cases hExec
      exact hLookup

theorem NativePrimCallPreservesWord_keccak256
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.KECCAK256
          [offset, size] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      rw [primCall_keccak256_ok] at hExec
      cases hKeccak : state.toMachineState.keccak256 offset size with
      | mk value machineState' =>
          simp [hKeccak] at hExec
          cases hExec
          subst final
          rw [state_getElem_setMachineState]
          exact hLookup

theorem NativePrimCallPreservesWord_keccak256_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.KECCAK256 values =
          .ok (final, rets) →
        final[name]! = expected :=
  NativePrimCallPreservesWord_binary_same_state_values EvmYul.Operation.KECCAK256
    name expected
    (by intro fuel state; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_keccak256_nil_invalid])
    (by intro fuel state offset; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_keccak256_singleton_invalid])
    (by intro fuel state offset size extra rest; cases fuel <;>
      simp [EvmYul.Yul.primCall, step_keccak256_overarity_invalid])
    (fun offset size =>
      NativePrimCallPreservesWord_keccak256 name expected offset size)

theorem NativePrimCallPreservesWord_log0
    (name : EvmYul.Identifier)
    (expected offset size : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG0 [offset, size] =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log0_ok fuel' state offset size hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log1
    (name : EvmYul.Identifier)
    (expected offset size topic0 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG1
          [offset, size, topic0] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log1_ok fuel' state offset size topic0 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log2
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG2
          [offset, size, topic0, topic1] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log2_ok fuel' state offset size topic0 topic1 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log3
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 topic2 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG3
          [offset, size, topic0, topic1, topic2] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log3_ok fuel' state offset size topic0 topic1 topic2 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_log4
    (name : EvmYul.Identifier)
    (expected offset size topic0 topic1 topic2 topic3 : EvmYul.Literal) :
    ∀ fuel state final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG4
          [offset, size, topic0, topic1, topic2, topic3] = .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state final rets hLookup hExec
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.primCall] at hExec
  | succ fuel' =>
      by_cases hPerm : state.executionEnv.perm = true
      · rw [primCall_log4_ok fuel' state offset size topic0 topic1 topic2 topic3 hPerm] at hExec
        cases hExec
        rw [state_getElem_setSharedState]
        exact hLookup
      · have hPermFalse : state.executionEnv.perm = false := by
          cases hp : state.executionEnv.perm
          · rfl
          · exact False.elim (hPerm hp)
        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
        cases hExec

theorem NativePrimCallPreservesWord_noop_result
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    {state final : EvmYul.Yul.State}
    {rets : List EvmYul.Literal}
    (hLookup : state[name]! = expected)
    (hExec : state = final ∧ rets = []) :
    final[name]! = expected := by
  rcases hExec with ⟨hFinal, _⟩
  subst final
  exact hLookup

theorem NativePrimCallPreservesWord_log0_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG0 values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm] at hExec
            exact NativePrimCallPreservesWord_noop_result
              name expected hLookup hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            cases hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                exact NativePrimCallPreservesWord_noop_result
                  name expected hLookup hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                cases hExec
      | cons size rest =>
          cases rest with
          | nil =>
              exact NativePrimCallPreservesWord_log0 name expected offset size
                fuel state final rets hLookup hExec
          | cons extra tail =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                    exact NativePrimCallPreservesWord_noop_result
                      name expected hLookup hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    cases hExec

theorem NativePrimCallPreservesWord_log1_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG1 values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm] at hExec
            exact NativePrimCallPreservesWord_noop_result
              name expected hLookup hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            cases hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                exact NativePrimCallPreservesWord_noop_result
                  name expected hLookup hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                cases hExec
      | cons size rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                    exact NativePrimCallPreservesWord_noop_result
                      name expected hLookup hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    cases hExec
          | cons topic0 rest =>
              cases rest with
              | nil =>
                  exact NativePrimCallPreservesWord_log1 name expected offset size
                    topic0 fuel state final rets hLookup hExec
              | cons extra tail =>
                  cases fuel with
                  | zero => simp [EvmYul.Yul.primCall] at hExec
                  | succ fuel' =>
                      by_cases hPerm : state.executionEnv.perm = true
                      · simp [EvmYul.Yul.primCall, hPerm] at hExec
                        exact NativePrimCallPreservesWord_noop_result
                          name expected hLookup hExec
                      · have hPermFalse : state.executionEnv.perm = false := by
                          cases hp : state.executionEnv.perm
                          · rfl
                          · exact False.elim (hPerm hp)
                        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                        cases hExec

theorem NativePrimCallPreservesWord_log2_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG2 values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm] at hExec
            exact NativePrimCallPreservesWord_noop_result
              name expected hLookup hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            cases hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                exact NativePrimCallPreservesWord_noop_result
                  name expected hLookup hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                cases hExec
      | cons size rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                    exact NativePrimCallPreservesWord_noop_result
                      name expected hLookup hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    cases hExec
          | cons topic0 rest =>
              cases rest with
              | nil =>
                  cases fuel with
                  | zero => simp [EvmYul.Yul.primCall] at hExec
                  | succ fuel' =>
                      by_cases hPerm : state.executionEnv.perm = true
                      · simp [EvmYul.Yul.primCall, hPerm] at hExec
                        exact NativePrimCallPreservesWord_noop_result
                          name expected hLookup hExec
                      · have hPermFalse : state.executionEnv.perm = false := by
                          cases hp : state.executionEnv.perm
                          · rfl
                          · exact False.elim (hPerm hp)
                        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                        cases hExec
              | cons topic1 rest =>
                  cases rest with
                  | nil =>
                      exact NativePrimCallPreservesWord_log2 name expected
                        offset size topic0 topic1 fuel state final rets hLookup
                        hExec
                  | cons extra tail =>
                      cases fuel with
                      | zero => simp [EvmYul.Yul.primCall] at hExec
                      | succ fuel' =>
                          by_cases hPerm : state.executionEnv.perm = true
                          · simp [EvmYul.Yul.primCall, hPerm] at hExec
                            exact NativePrimCallPreservesWord_noop_result
                              name expected hLookup hExec
                          · have hPermFalse :
                                state.executionEnv.perm = false := by
                              cases hp : state.executionEnv.perm
                              · rfl
                              · exact False.elim (hPerm hp)
                            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                            cases hExec

theorem NativePrimCallPreservesWord_log3_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG3 values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm] at hExec
            exact NativePrimCallPreservesWord_noop_result
              name expected hLookup hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            cases hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                exact NativePrimCallPreservesWord_noop_result
                  name expected hLookup hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                cases hExec
      | cons size rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                    exact NativePrimCallPreservesWord_noop_result
                      name expected hLookup hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    cases hExec
          | cons topic0 rest =>
              cases rest with
              | nil =>
                  cases fuel with
                  | zero => simp [EvmYul.Yul.primCall] at hExec
                  | succ fuel' =>
                      by_cases hPerm : state.executionEnv.perm = true
                      · simp [EvmYul.Yul.primCall, hPerm] at hExec
                        exact NativePrimCallPreservesWord_noop_result
                          name expected hLookup hExec
                      · have hPermFalse : state.executionEnv.perm = false := by
                          cases hp : state.executionEnv.perm
                          · rfl
                          · exact False.elim (hPerm hp)
                        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                        cases hExec
              | cons topic1 rest =>
                  cases rest with
                  | nil =>
                      cases fuel with
                      | zero => simp [EvmYul.Yul.primCall] at hExec
                      | succ fuel' =>
                          by_cases hPerm : state.executionEnv.perm = true
                          · simp [EvmYul.Yul.primCall, hPerm] at hExec
                            exact NativePrimCallPreservesWord_noop_result
                              name expected hLookup hExec
                          · have hPermFalse :
                                state.executionEnv.perm = false := by
                              cases hp : state.executionEnv.perm
                              · rfl
                              · exact False.elim (hPerm hp)
                            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                            cases hExec
                  | cons topic2 rest =>
                      cases rest with
                      | nil =>
                          exact NativePrimCallPreservesWord_log3 name expected
                            offset size topic0 topic1 topic2 fuel state final
                            rets hLookup hExec
                      | cons extra tail =>
                          cases fuel with
                          | zero => simp [EvmYul.Yul.primCall] at hExec
                          | succ fuel' =>
                              by_cases hPerm :
                                  state.executionEnv.perm = true
                              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                                exact NativePrimCallPreservesWord_noop_result
                                  name expected hLookup hExec
                              · have hPermFalse :
                                    state.executionEnv.perm = false := by
                                  cases hp : state.executionEnv.perm
                                  · rfl
                                  · exact False.elim (hPerm hp)
                                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                                cases hExec

theorem NativePrimCallPreservesWord_log4_values
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state EvmYul.Operation.LOG4 values =
          .ok (final, rets) →
        final[name]! = expected := by
  intro fuel state values final rets hLookup hExec
  cases values with
  | nil =>
      cases fuel with
      | zero => simp [EvmYul.Yul.primCall] at hExec
      | succ fuel' =>
          by_cases hPerm : state.executionEnv.perm = true
          · simp [EvmYul.Yul.primCall, hPerm] at hExec
            exact NativePrimCallPreservesWord_noop_result
              name expected hLookup hExec
          · have hPermFalse : state.executionEnv.perm = false := by
              cases hp : state.executionEnv.perm
              · rfl
              · exact False.elim (hPerm hp)
            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
            cases hExec
  | cons offset rest =>
      cases rest with
      | nil =>
          cases fuel with
          | zero => simp [EvmYul.Yul.primCall] at hExec
          | succ fuel' =>
              by_cases hPerm : state.executionEnv.perm = true
              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                exact NativePrimCallPreservesWord_noop_result
                  name expected hLookup hExec
              · have hPermFalse : state.executionEnv.perm = false := by
                  cases hp : state.executionEnv.perm
                  · rfl
                  · exact False.elim (hPerm hp)
                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                cases hExec
      | cons size rest =>
          cases rest with
          | nil =>
              cases fuel with
              | zero => simp [EvmYul.Yul.primCall] at hExec
              | succ fuel' =>
                  by_cases hPerm : state.executionEnv.perm = true
                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                    exact NativePrimCallPreservesWord_noop_result
                      name expected hLookup hExec
                  · have hPermFalse : state.executionEnv.perm = false := by
                      cases hp : state.executionEnv.perm
                      · rfl
                      · exact False.elim (hPerm hp)
                    simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                    cases hExec
          | cons topic0 rest =>
              cases rest with
              | nil =>
                  cases fuel with
                  | zero => simp [EvmYul.Yul.primCall] at hExec
                  | succ fuel' =>
                      by_cases hPerm : state.executionEnv.perm = true
                      · simp [EvmYul.Yul.primCall, hPerm] at hExec
                        exact NativePrimCallPreservesWord_noop_result
                          name expected hLookup hExec
                      · have hPermFalse : state.executionEnv.perm = false := by
                          cases hp : state.executionEnv.perm
                          · rfl
                          · exact False.elim (hPerm hp)
                        simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                        cases hExec
              | cons topic1 rest =>
                  cases rest with
                  | nil =>
                      cases fuel with
                      | zero => simp [EvmYul.Yul.primCall] at hExec
                      | succ fuel' =>
                          by_cases hPerm :
                              state.executionEnv.perm = true
                          · simp [EvmYul.Yul.primCall, hPerm] at hExec
                            exact NativePrimCallPreservesWord_noop_result
                              name expected hLookup hExec
                          · have hPermFalse :
                                state.executionEnv.perm = false := by
                              cases hp : state.executionEnv.perm
                              · rfl
                              · exact False.elim (hPerm hp)
                            simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                            cases hExec
                  | cons topic2 rest =>
                      cases rest with
                      | nil =>
                          cases fuel with
                          | zero => simp [EvmYul.Yul.primCall] at hExec
                          | succ fuel' =>
                              by_cases hPerm :
                                  state.executionEnv.perm = true
                              · simp [EvmYul.Yul.primCall, hPerm] at hExec
                                exact NativePrimCallPreservesWord_noop_result
                                  name expected hLookup hExec
                              · have hPermFalse :
                                    state.executionEnv.perm = false := by
                                  cases hp : state.executionEnv.perm
                                  · rfl
                                  · exact False.elim (hPerm hp)
                                simp [EvmYul.Yul.primCall, hPermFalse] at hExec
                                cases hExec
                      | cons topic3 rest =>
                          cases rest with
                          | nil =>
                              exact NativePrimCallPreservesWord_log4 name
                                expected offset size topic0 topic1 topic2 topic3
                                fuel state final rets hLookup hExec
                          | cons extra tail =>
                              cases fuel with
                              | zero => simp [EvmYul.Yul.primCall] at hExec
                              | succ fuel' =>
                                  by_cases hPerm :
                                      state.executionEnv.perm = true
                                  · simp [EvmYul.Yul.primCall, hPerm] at hExec
                                    exact NativePrimCallPreservesWord_noop_result
                                      name expected hLookup hExec
                                  · have hPermFalse :
                                        state.executionEnv.perm = false := by
                                      cases hp : state.executionEnv.perm
                                      · rfl
                                      · exact False.elim (hPerm hp)
                                    simp [EvmYul.Yul.primCall, hPermFalse]
                                      at hExec
                                    cases hExec

theorem lookupRuntimePrimOp_ne_none_of_allowed_of_ne_mappingSlot
    (func : EvmYul.Identifier)
    (hAllowed :
      Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
    (hNeMapping : func ≠ "mappingSlot") :
    Backends.lookupRuntimePrimOp func ≠ none := by
  simp only [Compiler.Proofs.YulGeneration.Backends.allowedExprCallName,
    Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hAllowed
  rcases hAllowed with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Backends.lookupRuntimePrimOp_add,
      Backends.lookupRuntimePrimOp_sub, Backends.lookupRuntimePrimOp_mul,
      Backends.lookupRuntimePrimOp_div, Backends.lookupRuntimePrimOp_mod,
      Backends.lookupRuntimePrimOp_lt, Backends.lookupRuntimePrimOp_gt,
      Backends.lookupRuntimePrimOp_eq, Backends.lookupRuntimePrimOp_iszero,
      Backends.lookupRuntimePrimOp_and, Backends.lookupRuntimePrimOp_or,
      Backends.lookupRuntimePrimOp_xor, Backends.lookupRuntimePrimOp_not,
      Backends.lookupRuntimePrimOp_shl, Backends.lookupRuntimePrimOp_shr,
      Backends.lookupRuntimePrimOp_addmod, Backends.lookupRuntimePrimOp_mulmod,
      Backends.lookupRuntimePrimOp_byte, Backends.lookupRuntimePrimOp_slt,
      Backends.lookupRuntimePrimOp_sgt, Backends.lookupRuntimePrimOp_exp,
      Backends.lookupRuntimePrimOp_sdiv, Backends.lookupRuntimePrimOp_smod,
      Backends.lookupRuntimePrimOp_sar, Backends.lookupRuntimePrimOp_signextend,
      Backends.lookupRuntimePrimOp_caller, Backends.lookupRuntimePrimOp_origin,
      Backends.lookupRuntimePrimOp_address, Backends.lookupRuntimePrimOp_callvalue,
      Backends.lookupRuntimePrimOp_timestamp, Backends.lookupRuntimePrimOp_number,
      Backends.lookupRuntimePrimOp_chainid, Backends.lookupRuntimePrimOp_blobbasefee,
      Backends.lookupRuntimePrimOp_calldataload,
      Backends.lookupRuntimePrimOp_calldatasize,
      Backends.lookupRuntimePrimOp_sload, Backends.lookupRuntimePrimOp_mappingSlot,
      Backends.lookupRuntimePrimOp_tload, Backends.lookupRuntimePrimOp_mload,
      Backends.lookupRuntimePrimOp_keccak256]
  all_goals first | contradiction | decide

theorem NativePrimCallPreservesWord_of_allowed_lookupRuntimePrimOp
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (op : EvmYul.Operation .Yul)
    (hAllowed :
      Compiler.Proofs.YulGeneration.Backends.allowedExprCallName func)
    (hOp : Backends.lookupRuntimePrimOp func = some op) :
    ∀ fuel state values final rets,
      state[name]! = expected →
        EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
        final[name]! = expected := by
  simp only [Compiler.Proofs.YulGeneration.Backends.allowedExprCallName,
    Compiler.Proofs.YulGeneration.Backends.bridgedBuiltins,
    List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hAllowed
  rcases hAllowed with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [Backends.lookupRuntimePrimOp_add,
      Backends.lookupRuntimePrimOp_sub, Backends.lookupRuntimePrimOp_mul,
      Backends.lookupRuntimePrimOp_div, Backends.lookupRuntimePrimOp_mod,
      Backends.lookupRuntimePrimOp_lt, Backends.lookupRuntimePrimOp_gt,
      Backends.lookupRuntimePrimOp_eq, Backends.lookupRuntimePrimOp_iszero,
      Backends.lookupRuntimePrimOp_and, Backends.lookupRuntimePrimOp_or,
      Backends.lookupRuntimePrimOp_xor, Backends.lookupRuntimePrimOp_not,
      Backends.lookupRuntimePrimOp_shl, Backends.lookupRuntimePrimOp_shr,
      Backends.lookupRuntimePrimOp_addmod, Backends.lookupRuntimePrimOp_mulmod,
      Backends.lookupRuntimePrimOp_byte, Backends.lookupRuntimePrimOp_slt,
      Backends.lookupRuntimePrimOp_sgt, Backends.lookupRuntimePrimOp_exp,
      Backends.lookupRuntimePrimOp_sdiv, Backends.lookupRuntimePrimOp_smod,
      Backends.lookupRuntimePrimOp_sar, Backends.lookupRuntimePrimOp_signextend,
      Backends.lookupRuntimePrimOp_caller, Backends.lookupRuntimePrimOp_origin,
      Backends.lookupRuntimePrimOp_address, Backends.lookupRuntimePrimOp_callvalue,
      Backends.lookupRuntimePrimOp_timestamp, Backends.lookupRuntimePrimOp_number,
      Backends.lookupRuntimePrimOp_chainid, Backends.lookupRuntimePrimOp_blobbasefee,
      Backends.lookupRuntimePrimOp_calldataload,
      Backends.lookupRuntimePrimOp_calldatasize,
      Backends.lookupRuntimePrimOp_sload, Backends.lookupRuntimePrimOp_mappingSlot,
      Backends.lookupRuntimePrimOp_tload, Backends.lookupRuntimePrimOp_mload,
      Backends.lookupRuntimePrimOp_keccak256, Option.some.injEq] at hOp
  all_goals cases hOp
  all_goals first
    | exact NativePrimCallPreservesWord_add_values name expected
    | exact NativePrimCallPreservesWord_sub_values name expected
    | exact NativePrimCallPreservesWord_mul_values name expected
    | exact NativePrimCallPreservesWord_div_values name expected
    | exact NativePrimCallPreservesWord_sdiv_values name expected
    | exact NativePrimCallPreservesWord_mod_values name expected
    | exact NativePrimCallPreservesWord_smod_values name expected
    | exact NativePrimCallPreservesWord_addmod_values name expected
    | exact NativePrimCallPreservesWord_mulmod_values name expected
    | exact NativePrimCallPreservesWord_exp_values name expected
    | exact NativePrimCallPreservesWord_signextend_values name expected
    | exact NativePrimCallPreservesWord_lt_values name expected
    | exact NativePrimCallPreservesWord_gt_values name expected
    | exact NativePrimCallPreservesWord_slt_values name expected
    | exact NativePrimCallPreservesWord_sgt_values name expected
    | exact NativePrimCallPreservesWord_eq_values name expected
    | exact NativePrimCallPreservesWord_iszero_values name expected
    | exact NativePrimCallPreservesWord_and_values name expected
    | exact NativePrimCallPreservesWord_or_values name expected
    | exact NativePrimCallPreservesWord_xor_values name expected
    | exact NativePrimCallPreservesWord_not_values name expected
    | exact NativePrimCallPreservesWord_byte_values name expected
    | exact NativePrimCallPreservesWord_shl_values name expected
    | exact NativePrimCallPreservesWord_shr_values name expected
    | exact NativePrimCallPreservesWord_sar_values name expected
    | exact NativePrimCallPreservesWord_keccak256_values name expected
    | exact NativePrimCallPreservesWord_address_values name expected
    | exact NativePrimCallPreservesWord_caller_values name expected
    | exact NativePrimCallPreservesWord_origin_values name expected
    | exact NativePrimCallPreservesWord_callvalue_values name expected
    | exact NativePrimCallPreservesWord_calldataload_values name expected
    | exact NativePrimCallPreservesWord_calldatasize_values name expected
    | exact NativePrimCallPreservesWord_timestamp_values name expected
    | exact NativePrimCallPreservesWord_number_values name expected
    | exact NativePrimCallPreservesWord_chainid_values name expected
    | exact NativePrimCallPreservesWord_blobbasefee_values name expected
    | exact NativePrimCallPreservesWord_mload_values name expected
    | exact NativePrimCallPreservesWord_sload_values name expected
    | exact NativePrimCallPreservesWord_tload_values name expected

theorem NativeExprPreservesWord_var
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected (.Var identifier) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeExprPreservesWord_lit
    (name : EvmYul.Identifier)
    (expected value : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected (.Lit value) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeEvalArgsPreservesWord_nil
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeEvalArgsPreservesWord name expected [] codeOverride := by
  intro fuel state final results hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.evalArgs] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.evalArgs] at hEval
      rcases hEval with ⟨hFinal, _⟩
      subst final
      exact hLookup

theorem NativeEvalArgsPreservesWord_cons
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (arg : EvmYul.Yul.Ast.Expr)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArg : NativeExprPreservesWord name expected arg codeOverride)
    (hArgs : NativeEvalArgsPreservesWord name expected args codeOverride) :
    NativeEvalArgsPreservesWord name expected (arg :: args) codeOverride := by
  intro fuel state final results hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.evalArgs] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.evalArgs] at hEval
      cases hEvalArg : EvmYul.Yul.eval fuel' arg codeOverride state with
      | error err =>
          rw [hEvalArg] at hEval
          cases fuel' <;> simp [EvmYul.Yul.evalTail] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, argValue⟩
          have hArgLookup : argState[name]! = expected :=
            hArg fuel' state argState argValue hLookup hEvalArg
          simp [hEvalArg] at hEval
          cases fuel' with
          | zero =>
              change
                EvmYul.Yul.evalTail 0 args codeOverride
                  (.ok (argState, argValue)) = .ok (final, results) at hEval
              simp [EvmYul.Yul.evalTail] at hEval
          | succ tailFuel =>
              change
                EvmYul.Yul.evalTail (Nat.succ tailFuel) args codeOverride
                  (.ok (argState, argValue)) = .ok (final, results) at hEval
              simp [EvmYul.Yul.evalTail] at hEval
              cases hEvalArgs :
                  EvmYul.Yul.evalArgs tailFuel args codeOverride argState with
              | error err =>
                  simp [hEvalArgs, EvmYul.Yul.cons'] at hEval
              | ok argsResult =>
                  rcases argsResult with ⟨argsState, values⟩
                  simp [hEvalArgs, EvmYul.Yul.cons'] at hEval
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hArgs tailFuel argState argsState values
                    hArgLookup hEvalArgs

theorem NativeEvalArgsPreservesWord_map_lowerExprNative
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ arg, arg ∈ args →
        NativeExprPreservesWord name expected
          (Backends.lowerExprNative arg) codeOverride) :
    NativeEvalArgsPreservesWord name expected
      (args.map Backends.lowerExprNative) codeOverride := by
  induction args with
  | nil =>
      exact NativeEvalArgsPreservesWord_nil name expected codeOverride
  | cons arg rest ih =>
      exact NativeEvalArgsPreservesWord_cons name expected
        (Backends.lowerExprNative arg) (rest.map Backends.lowerExprNative)
        codeOverride
        (hArgs arg (by simp))
        (ih (by
          intro restArg hRest
          exact hArgs restArg (by simp [hRest])))

theorem NativeEvalArgsPreservesWord_map_lowerExprNative_reverse
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs :
      ∀ arg, arg ∈ args →
        NativeExprPreservesWord name expected
          (Backends.lowerExprNative arg) codeOverride) :
    NativeEvalArgsPreservesWord name expected
      ((args.map Backends.lowerExprNative).reverse) codeOverride := by
  simpa [List.map_reverse] using
    NativeEvalArgsPreservesWord_map_lowerExprNative name expected
      args.reverse codeOverride
      (by
        intro arg hArg
        exact hArgs arg (by simpa using hArg))

theorem NativeExprPreservesWord_lowerExprNative_lit
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.lit value)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_lit name expected (EvmYul.UInt256.ofNat value)
      codeOverride

theorem NativeExprPreservesWord_lowerExprNative_hex
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (value : Nat)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.hex value)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_lit name expected (EvmYul.UInt256.ofNat value)
      codeOverride

theorem NativeExprPreservesWord_lowerExprNative_str
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.str identifier)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_var name expected identifier codeOverride

theorem NativeExprPreservesWord_lowerExprNative_ident
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (identifier : EvmYul.Identifier)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.ident identifier)) codeOverride := by
  simpa [Backends.lowerExprNative] using
    NativeExprPreservesWord_var name expected identifier codeOverride

theorem NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (.Call (Sum.inl prim) args) codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      cases hEvalArgs :
          EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          rw [hEvalArgs] at hEval
          simp [EvmYul.Yul.reverse', EvmYul.Yul.evalPrimCall] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          rw [hEvalArgs] at hEval
          simp [EvmYul.Yul.reverse', EvmYul.Yul.evalPrimCall] at hEval
          cases hPrimCall :
              EvmYul.Yul.primCall fuel' argState prim values.reverse with
          | error err =>
              simp [hPrimCall, EvmYul.Yul.head'] at hEval
          | ok primResult =>
              rcases primResult with ⟨primState, rets⟩
              simp [hPrimCall, EvmYul.Yul.head'] at hEval
              cases rets with
              | nil =>
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hPrim fuel' argState values.reverse primState []
                    hArgLookup hPrimCall
              | cons ret rest =>
                  rcases hEval with ⟨hFinal, _⟩
                  subst final
                  exact hPrim fuel' argState values.reverse primState (ret :: rest)
                    hArgLookup hPrimCall

theorem NativeExprPreservesWord_call_prim_of_nativeEvalArgs_primCall_preserves
    (name : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (prim : EvmYul.Yul.Ast.PrimOp)
    (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state prim values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (.Call (Sum.inl prim) args) codeOverride :=
  NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves
    name expected prim args codeOverride hArgs hPrim

theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride := by
  rw [Backends.lowerExprNative_call_runtimePrimOp func args op hOp]
  exact NativeExprPreservesWord_call_prim_of_evalArgs_primCall_preserves
    name expected op (args.map Backends.lowerExprNative) codeOverride hArgs
    hPrim

theorem NativeExprPreservesWord_call_user_of_evalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hCall :
      ∀ fuel state values final rets, state[name]! = expected →
        EvmYul.Yul.call fuel values (some functionName) codeOverride state =
          .ok (final, rets) → final[name]! = expected) :
    NativeExprPreservesWord name expected (.Call (Sum.inr functionName) args)
      codeOverride := by
  intro fuel state final result hLookup hEval
  cases fuel with
  | zero =>
      simp [EvmYul.Yul.eval] at hEval
  | succ fuel' =>
      simp [EvmYul.Yul.eval] at hEval
      cases hEvalArgs : EvmYul.Yul.evalArgs fuel' args.reverse codeOverride state with
      | error err =>
          rw [hEvalArgs] at hEval
          cases fuel' <;>
            simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
      | ok argResult =>
          rcases argResult with ⟨argState, values⟩
          have hArgLookup : argState[name]! = expected :=
            hArgs fuel' state argState values hLookup hEvalArgs
          rw [hEvalArgs] at hEval
          cases fuel' with
          | zero => simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
          | succ callFuel =>
              simp [EvmYul.Yul.reverse', EvmYul.Yul.evalCall] at hEval
              cases hUserCall :
                  EvmYul.Yul.call callFuel values.reverse (some functionName)
                    codeOverride argState with
              | error err =>
                  simp [hUserCall, EvmYul.Yul.head'] at hEval
              | ok callResult =>
                  rcases callResult with ⟨callState, rets⟩
                  simp [hUserCall, EvmYul.Yul.head'] at hEval
                  cases rets with
                  | nil =>
                      rcases hEval with ⟨rfl, _⟩
                      exact hCall callFuel argState values.reverse callState []
                        hArgLookup hUserCall
                  | cons ret rest =>
                      rcases hEval with ⟨rfl, _⟩
                      exact hCall callFuel argState values.reverse callState
                        (ret :: rest) hArgLookup hUserCall

theorem NativeExprPreservesWord_call_user_of_nativeEvalArgs_call_preserves
    (name : EvmYul.Identifier) (expected : EvmYul.Literal)
    (functionName : EvmYul.Yul.Ast.YulFunctionName) (args : List EvmYul.Yul.Ast.Expr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hArgs : NativeEvalArgsPreservesWord name expected args.reverse codeOverride)
    (hCall :
      ∀ fuel state values final rets, state[name]! = expected →
        EvmYul.Yul.call fuel values (some functionName) codeOverride state =
          .ok (final, rets) → final[name]! = expected) :
    NativeExprPreservesWord name expected (.Call (Sum.inr functionName) args)
      codeOverride :=
  NativeExprPreservesWord_call_user_of_evalArgs_call_preserves
    name expected functionName args codeOverride hArgs hCall

theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride := by
  rw [Backends.lowerExprNative_call_userFunction func args hOp]
  exact NativeExprPreservesWord_call_user_of_evalArgs_call_preserves
    name expected func (args.map Backends.lowerExprNative) codeOverride hArgs
    hCall

theorem NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_nativeEvalArgs_primCall_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (op : EvmYul.Operation .Yul)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = some op)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hPrim :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.primCall fuel state op values = .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride :=
  NativeExprPreservesWord_lowerExprNative_call_runtimePrimOp_of_evalArgs_primCall_preserves
    name func expected args op codeOverride hOp hArgs hPrim

theorem NativeExprPreservesWord_lowerExprNative_call_userFunction_of_nativeEvalArgs_call_preserves
    (name func : EvmYul.Identifier)
    (expected : EvmYul.Literal)
    (args : List YulExpr)
    (codeOverride : Option EvmYul.Yul.Ast.YulContract)
    (hOp : Backends.lookupRuntimePrimOp func = none)
    (hArgs :
      NativeEvalArgsPreservesWord name expected
        ((args.map Backends.lowerExprNative).reverse) codeOverride)
    (hCall :
      ∀ fuel state values final rets,
        state[name]! = expected →
          EvmYul.Yul.call fuel values (some func) codeOverride state =
            .ok (final, rets) →
          final[name]! = expected) :
    NativeExprPreservesWord name expected
      (Backends.lowerExprNative (.call func args)) codeOverride :=
  NativeExprPreservesWord_lowerExprNative_call_userFunction_of_evalArgs_call_preserves
    name func expected args codeOverride hOp hArgs hCall


end Compiler.Proofs.YulGeneration.Backends.Native
