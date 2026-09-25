import TranslationValidationCapturedExecution
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness.Foundation

-- Resolve the native Literal/Identifier aliases when reusing lookup lemmas.
-- This changes elaboration transparency, not the kernel's proof checking.
set_option backward.isDefEq.respectTransparency false

namespace SolidityTranslationValidation.AstBridge

open EvmYul Yul
open Compiler.Proofs.YulGeneration.Backends
open Compiler.Proofs.YulGeneration.Backends.Native

private theorem word_ext {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  congr 1
  exact Fin.ext h

private theorem native_zero_eq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := by rfl

private theorem native_product_word (x y : Nat) (hx : x < UInt256.size) (hy : y < UInt256.size) :
    UInt256.mul (UInt256.ofNat x) (UInt256.ofNat y) = UInt256.ofNat (x * y) := by
  apply word_ext
  change (x % UInt256.size * (y % UInt256.size)) % UInt256.size = (x * y) % UInt256.size
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

private theorem native_division_word (p d : Nat) (hp : p < UInt256.size) (hd : d < UInt256.size) :
    UInt256.div (UInt256.ofNat p) (UInt256.ofNat d) = UInt256.ofNat (p / d) := by
  apply word_ext
  change (p % UInt256.size) / (d % UInt256.size) = (p / d) % UInt256.size
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hd,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hp)]

private theorem native_iszero_word (x : Nat) (hx : x < UInt256.size) :
    UInt256.isZero (UInt256.ofNat x) = UInt256.ofNat (if x = 0 then 1 else 0) := by
  by_cases hz : x = 0
  · subst x
    decide
  · have heq : (UInt256.ofNat x == UInt256.ofNat 0) = false := by
      simp [BEq.beq, EvmYul.instBEqUInt256.beq, UInt256.ofNat, Id.run]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hz) hx
    unfold UInt256.isZero UInt256.eq0
    change Bool.toUInt256 (UInt256.ofNat x == UInt256.ofNat 0) = _
    rw [heq, if_neg hz]
    rfl

private theorem native_overflow_guard_zero (x y : Nat)
    (hx : x < UInt256.size) (_hy : y < UInt256.size) (hfit : x * y < UInt256.size) :
    UInt256.isZero (UInt256.lor (UInt256.isZero (UInt256.ofNat x))
      (UInt256.eq (UInt256.ofNat y)
        (UInt256.div (UInt256.ofNat (x * y)) (UInt256.ofNat x)))) = UInt256.ofNat 0 := by
  rw [native_iszero_word x hx]
  by_cases hz : x = 0
  · subst x
    simp only [ite_true]
    unfold UInt256.eq UInt256.fromBool Bool.toUInt256
    split <;> decide
  · rw [if_neg hz, native_division_word (x * y) x hfit hx,
      Nat.mul_div_cancel_left y (Nat.pos_of_ne_zero hz)]
    simp [UInt256.eq]
    decide

theorem variableValue_insert_self (shared : SharedState .Yul) (store : Yul.VarStore)
    (name : String) (value : UInt256) :
    variableValue ((Yul.State.Ok shared store).insert name value) name = value := by
  simp [variableValue, Yul.eval, Yul.State.insert, Yul.State.lookup!, Yul.State.store,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem]

theorem variableValue_insert_other (s : Yul.State) (name other : String)
    (value : UInt256) (hne : name ≠ other) :
    variableValue (s.insert other value) name = variableValue s name := by
  cases s with
  | Ok shared store =>
    simp [variableValue, Yul.eval, Yul.State.insert, Yul.State.lookup!, Yul.State.store,
      GetElem?.getElem!, decidableGetElem?, GetElem.getElem]
    by_cases hmem : name ∈ store
    · simp [hmem, hne, Finmap.lookup_insert_of_ne store hne]
    · simp [hmem, hne]
  | OutOfFuel => rfl
  | Checkpoint jump => rfl

theorem eval_overflow_condition (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) :
    Yul.eval (fuel + 20) capturedOverflowGuardCondition code s =
      .ok (s, UInt256.isZero (UInt256.lor (UInt256.isZero (variableValue s "value"))
        (UInt256.eq (variableValue s "value_1")
          (UInt256.div (variableValue s "product") (variableValue s "value"))))) := by
  simp [variableValue, capturedOverflowGuardCondition, Yul.eval, Yul.evalArgs,
    Yul.evalTail, Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head']

theorem eval_denominator_condition (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) :
    Yul.eval (fuel + 20) capturedDenominatorGuardCondition code s =
      .ok (s, UInt256.isZero (variableValue s "value_2")) := by
  simp [variableValue, capturedDenominatorGuardCondition, Yul.eval, Yul.evalArgs,
    Yul.evalTail, Yul.evalPrimCall, Yul.reverse', Yul.cons', Yul.head']

theorem overflow_guard_passes (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) (x y : Nat)
    (hx : x < UInt256.size) (hy : y < UInt256.size) (hfit : x * y < UInt256.size)
    (hX : variableValue s "value" = UInt256.ofNat x)
    (hY : variableValue s "value_1" = UInt256.ofNat y)
    (hP : variableValue s "product" = UInt256.ofNat (x * y)) :
    Yul.exec (fuel + 21) capturedOverflowGuard code s = .ok s := by
  have hcondition : Yul.eval (fuel + 20) capturedOverflowGuardCondition code s =
      .ok (s, UInt256.ofNat 0) := by
    rw [eval_overflow_condition, hX, hY, hP, native_overflow_guard_zero x y hx hy hfit]
  unfold capturedOverflowGuardCondition at hcondition
  simp [capturedOverflowGuard, Yul.exec, hcondition, native_zero_eq]

theorem denominator_guard_passes (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) (d : Nat) (hd : d < UInt256.size) (hdzero : d ≠ 0)
    (hD : variableValue s "value_2" = UInt256.ofNat d) :
    Yul.exec (fuel + 21) capturedDenominatorGuard code s = .ok s := by
  have hcondition : Yul.eval (fuel + 20) capturedDenominatorGuardCondition code s =
      .ok (s, UInt256.ofNat 0) := by
    rw [eval_denominator_condition, hD, native_iszero_word d hd, if_neg hdzero]
  unfold capturedDenominatorGuardCondition at hcondition
  simp [capturedDenominatorGuard, Yul.exec, hcondition, native_zero_eq]

theorem exec_product_with_fuel (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 10) capturedProductDeclaration code s =
      .ok (s.insert "product"
        (UInt256.mul (variableValue s "value") (variableValue s "value_1"))) := by
  simp [capturedProductDeclaration, capturedProductExpr, variableValue,
    Yul.exec, Yul.eval, Yul.evalArgs, Yul.evalTail,
    Yul.execPrimCall, Yul.reverse', Yul.cons', Yul.multifill']
  cases s <;> rfl

/-- Execute the actual contiguous product/overflow/division-check statements.
The only state change is insertion of the correctly computed product local.
Both captured panic bodies remain in the AST and are proved unreachable from
the arithmetic preconditions, rather than removed or assumed away. -/
theorem captured_guarded_prefix_continuation (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (x y d : Nat) (rest : List Yul.Ast.Stmt)
    (hx : x < UInt256.size) (hy : y < UInt256.size) (hd : d < UInt256.size)
    (hfit : x * y < UInt256.size) (hdzero : d ≠ 0)
    (hX : variableValue (.Ok shared store) "value" = UInt256.ofNat x)
    (hY : variableValue (.Ok shared store) "value_1" = UInt256.ofNat y)
    (hD : variableValue (.Ok shared store) "value_2" = UInt256.ofNat d) :
    Yul.exec 100 (.Block ([capturedProductDeclaration, capturedOverflowGuard,
      capturedDenominatorGuard] ++ rest)) code (.Ok shared store) =
      Yul.exec 97 (.Block rest) code
        ((Yul.State.Ok shared store).insert "product" (UInt256.ofNat (x * y))) := by
  let afterProduct := (Yul.State.Ok shared store).insert "product" (UInt256.ofNat (x * y))
  have productStep : Yul.exec 99 capturedProductDeclaration code (.Ok shared store) =
      .ok afterProduct := by
    rw [show 99 = 89 + 10 by rfl, exec_product_with_fuel, hX, hY, native_product_word x y hx hy]
  have hP' : variableValue afterProduct "product" = UInt256.ofNat (x * y) :=
    variableValue_insert_self shared store "product" _
  have hX' : variableValue afterProduct "value" = UInt256.ofNat x := by
    rw [variableValue_insert_other _ "value" "product" _ (by decide), hX]
  have hY' : variableValue afterProduct "value_1" = UInt256.ofNat y := by
    rw [variableValue_insert_other _ "value_1" "product" _ (by decide), hY]
  have hD' : variableValue afterProduct "value_2" = UInt256.ofNat d := by
    rw [variableValue_insert_other _ "value_2" "product" _ (by decide), hD]
  have overflowStep : Yul.exec 98 capturedOverflowGuard code afterProduct = .ok afterProduct :=
    overflow_guard_passes 77 afterProduct code x y hx hy hfit hX' hY' hP'
  have denominatorStep : Yul.exec 97 capturedDenominatorGuard code afterProduct = .ok afterProduct :=
    denominator_guard_passes 76 afterProduct code d hd hdzero hD'
  change Yul.exec 100 (.Block (capturedProductDeclaration :: capturedOverflowGuard ::
    capturedDenominatorGuard :: rest)) code (.Ok shared store) =
      Yul.exec 97 (.Block rest) code afterProduct
  rw [exec_block_cons_ok_eq 99 _ _ _ _ _ productStep,
    exec_block_cons_ok_eq 98 _ _ _ _ _ overflowStep,
    exec_block_cons_ok_eq 97 _ _ _ _ _ denominatorStep]

theorem captured_guarded_prefix_success (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (x y d : Nat)
    (hx : x < UInt256.size) (hy : y < UInt256.size) (hd : d < UInt256.size)
    (hfit : x * y < UInt256.size) (hdzero : d ≠ 0)
    (hX : variableValue (.Ok shared store) "value" = UInt256.ofNat x)
    (hY : variableValue (.Ok shared store) "value_1" = UInt256.ofNat y)
    (hD : variableValue (.Ok shared store) "value_2" = UInt256.ofNat d) :
    Yul.exec 100 capturedGuardedPrefix code (.Ok shared store) =
      .ok ((Yul.State.Ok shared store).insert "product" (UInt256.ofNat (x * y))) := by
  have h := captured_guarded_prefix_continuation shared store code x y d [] hx hy hd hfit hdzero hX hY hD
  rw [exec_block_nil_ok 96] at h
  exact h

theorem exec_captured_return_store (fuel : Nat) (s : Yul.State)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 20) capturedReturnStore code s =
      .ok (s.setMachineState (s.toMachineState.mstore (variableValue s "_1")
        (UInt256.div (variableValue s "product") (variableValue s "value_2")))) := by
  simp [capturedReturnStore, variableValue, Yul.exec, Yul.eval, Yul.evalArgs,
    Yul.evalTail, Yul.evalPrimCall, Yul.execPrimCall, Yul.reverse', Yul.cons',
    Yul.head', Yul.multifill']
  cases s <;> rfl

theorem exec_captured_return (fuel : Nat) (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) :
    Yul.exec (fuel + 20) capturedReturn code (.Ok shared store) =
      .error (.YulHalt
        ((Yul.State.Ok shared store).setMachineState
          (shared.toMachineState.evmReturn (variableValue (.Ok shared store) "_1") (UInt256.ofNat 32)))
        (UInt256.ofNat 1)) := by
  simp [capturedReturn, variableValue, Yul.exec, Yul.eval, Yul.evalArgs,
    Yul.evalTail, Yul.execPrimCall, Yul.reverse', Yul.cons',
    Yul.binaryMachineStateOp, Yul.State.toMachineState, Yul.State.setMachineState,
    Yul.multifill']
  rfl

private theorem variableValue_same_store (shared other : SharedState .Yul) (store : Yul.VarStore)
    (name : String) :
    variableValue (.Ok shared store) name = variableValue (.Ok other store) name := by
  simp [variableValue, Yul.eval, Yul.State.store, Yul.State.lookup!,
    GetElem?.getElem!, decidableGetElem?, GetElem.getElem]

/-- Expected native state after the actual return-word mstore and RETURN.
The definition uses the native byte-memory operations without replacing them
by a word-list or assuming what bytes they return. -/
def successfulBodyState (shared : SharedState .Yul) (store : Yul.VarStore) (x y d : Nat) : Yul.State :=
  let memoryState := shared.toMachineState.mstore (UInt256.ofNat 128) (UInt256.ofNat (x * y / d))
  let returnState := memoryState.evmReturn (UInt256.ofNat 128) (UInt256.ofNat 32)
  .Ok { shared with toMachineState := returnState }
    (store.insert "product" (UInt256.ofNat (x * y)))

/-- Execute the entire captured arithmetic body slice, including both intact
panic branches, mstore and RETURN. Inputs and memoryguard's pointer are entry
preconditions; this theorem does not execute the ABI/dispatcher prologue.
EVMYulLean represents a successful RETURN by the YulHalt exception constructor. -/
theorem captured_arithmetic_body_success (shared : SharedState .Yul) (store : Yul.VarStore)
    (code : Option Yul.Ast.YulContract) (x y d : Nat)
    (hx : x < UInt256.size) (hy : y < UInt256.size) (hd : d < UInt256.size)
    (hfit : x * y < UInt256.size) (hdzero : d ≠ 0)
    (hX : variableValue (.Ok shared store) "value" = UInt256.ofNat x)
    (hY : variableValue (.Ok shared store) "value_1" = UInt256.ofNat y)
    (hD : variableValue (.Ok shared store) "value_2" = UInt256.ofNat d)
    (hPtr : variableValue (.Ok shared store) "_1" = UInt256.ofNat 128) :
    Yul.exec 100 capturedArithmeticBody code (.Ok shared store) =
      .error (.YulHalt (successfulBodyState shared store x y d) (UInt256.ofNat 1)) := by
  let afterProduct := (Yul.State.Ok shared store).insert "product" (UInt256.ofNat (x * y))
  let writtenMachine := shared.toMachineState.mstore (UInt256.ofNat 128) (UInt256.ofNat (x * y / d))
  let writtenShared : SharedState .Yul := { shared with toMachineState := writtenMachine }
  let written := Yul.State.Ok writtenShared (store.insert "product" (UInt256.ofNat (x * y)))
  have hP' : variableValue afterProduct "product" = UInt256.ofNat (x * y) :=
    variableValue_insert_self shared store "product" _
  have hD' : variableValue afterProduct "value_2" = UInt256.ofNat d := by
    rw [variableValue_insert_other _ "value_2" "product" _ (by decide), hD]
  have hPtr' : variableValue afterProduct "_1" = UInt256.ofNat 128 := by
    rw [variableValue_insert_other _ "_1" "product" _ (by decide), hPtr]
  have storeStep : Yul.exec 96 capturedReturnStore code afterProduct = .ok written := by
    rw [show 96 = 76 + 20 by rfl, exec_captured_return_store, hP', hD', hPtr',
      native_division_word (x * y) d hfit hd]
    rfl
  have hWrittenPtr : variableValue written "_1" = UInt256.ofNat 128 := by
    rw [variableValue_same_store writtenShared shared]
    exact hPtr'
  have returnStep : Yul.exec 95 capturedReturn code written =
      .error (.YulHalt (successfulBodyState shared store x y d) (UInt256.ofNat 1)) := by
    rw [show 95 = 75 + 20 by rfl, exec_captured_return, hWrittenPtr]
    rfl
  change Yul.exec 100 (.Block ([capturedProductDeclaration, capturedOverflowGuard,
    capturedDenominatorGuard] ++ [capturedReturnStore, capturedReturn])) code (.Ok shared store) = _
  rw [captured_guarded_prefix_continuation shared store code x y d
    [capturedReturnStore, capturedReturn] hx hy hd hfit hdzero hX hY hD,
    exec_block_cons_ok_eq 96 _ _ _ _ _ storeStep]
  exact exec_block_cons_error 95 _ [] code written _ returnStep

#print axioms eval_overflow_condition
#print axioms overflow_guard_passes
#print axioms denominator_guard_passes
#print axioms captured_guarded_prefix_success
#print axioms captured_guarded_prefix_continuation
#print axioms exec_captured_return_store
#print axioms exec_captured_return
#print axioms captured_arithmetic_body_success
#print axioms decodeOverflowGuard
#print axioms decodeDenominatorGuard
#print axioms decodeReturnStore
#print axioms decodeReturn

end SolidityTranslationValidation.AstBridge
