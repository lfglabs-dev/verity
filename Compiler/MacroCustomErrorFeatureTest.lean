import Compiler.CompilationModel
import Contracts.Common

namespace Compiler.MacroCustomErrorFeatureTest

open Compiler.CompilationModel
open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

namespace MacroCustomErrorUsageSmoke

verity_contract MacroCustomErrorUsage where
  storage
    sentinel : Uint256 := slot 0

  errors
    error NonPositive(Uint256)
    error AmountTooLarge(Uint256, Uint256)

  function requirePositive (amount : Uint256) : Unit := do
    requireError (amount != 0) NonPositive(amount)

  function rejectLarge (amount : Uint256) : Unit := do
    if amount > 100 then
      revert AmountTooLarge(amount, 100)
    else
      pure ()

def requirePositiveModelUsesCustomErrorGuard : Bool :=
  match MacroCustomErrorUsage.requirePositive_modelBody with
  | [Stmt.requireError
        (Expr.logicalNot (Expr.eq (Expr.param "amount") (Expr.literal 0)))
        "NonPositive"
        [Expr.param "amount"],
      Stmt.stop] =>
      true
  | _ => false

example : requirePositiveModelUsesCustomErrorGuard = true := by native_decide

def rejectLargeModelUsesCustomErrorRevert : Bool :=
  match MacroCustomErrorUsage.rejectLarge_modelBody with
  | [Stmt.ite
        (Expr.gt (Expr.param "amount") (Expr.literal 100))
        [Stmt.revertError "AmountTooLarge" [Expr.param "amount", Expr.literal 100]]
        [],
      Stmt.stop] =>
      true
  | _ => false

example : rejectLargeModelUsesCustomErrorRevert = true := by native_decide

def requirePositiveExecutablePreservesSuccess : Bool :=
  match MacroCustomErrorUsage.requirePositive 7 Verity.defaultState with
  | .success () state => state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : requirePositiveExecutablePreservesSuccess = true := by native_decide

def rejectLargeExecutableUsesRuntimeFallback : Bool :=
  match MacroCustomErrorUsage.rejectLarge 101 Verity.defaultState with
  | .revert msg state =>
      msg == "AmountTooLarge(101, 100)" && state.sender == Verity.defaultState.sender
  | .success _ _ => false

example : rejectLargeExecutableUsesRuntimeFallback = true := by native_decide

end MacroCustomErrorUsageSmoke

namespace RequireSomeUintErrorSmoke

verity_contract RequireSomeUintErrorUsage where
  storage
    sentinel : Uint256 := slot 0

  errors
    error AddOverflow ()
    error SubUnderflow ()
    error DivByZero ()
    error MulOverflow (Uint256, Uint256)

  function checkAdd (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeAdd a b) AddOverflow()
    return result

  function checkSub (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeSub a b) SubUnderflow()
    return result

  function checkDiv (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeDiv a b) DivByZero()
    return result

  function checkMul (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeMul a b) MulOverflow(a, b)
    return result

def checkAddLowersToTypedRequireError : Bool :=
  match RequireSomeUintErrorUsage.checkAdd_modelBody with
  | [Stmt.requireError
        (Expr.ge (Expr.add (Expr.param "a") (Expr.param "b")) (Expr.param "a"))
        "AddOverflow"
        [],
      Stmt.letVar "result" (Expr.add (Expr.param "a") (Expr.param "b")),
      Stmt.return (Expr.localVar "result")] =>
      true
  | _ => false

example : checkAddLowersToTypedRequireError = true := by native_decide

def checkSubLowersToTypedRequireError : Bool :=
  match RequireSomeUintErrorUsage.checkSub_modelBody with
  | [Stmt.requireError
        (Expr.ge (Expr.param "a") (Expr.param "b"))
        "SubUnderflow"
        [],
      Stmt.letVar "result" (Expr.sub (Expr.param "a") (Expr.param "b")),
      Stmt.return (Expr.localVar "result")] =>
      true
  | _ => false

example : checkSubLowersToTypedRequireError = true := by native_decide

def checkDivLowersToTypedRequireError : Bool :=
  match RequireSomeUintErrorUsage.checkDiv_modelBody with
  | [Stmt.requireError
        (Expr.logicalNot (Expr.eq (Expr.param "b") (Expr.literal 0)))
        "DivByZero"
        [],
      Stmt.letVar "result" (Expr.div (Expr.param "a") (Expr.param "b")),
      Stmt.return (Expr.localVar "result")] =>
      true
  | _ => false

example : checkDivLowersToTypedRequireError = true := by native_decide

def checkMulLowersToTypedRequireError : Bool :=
  match RequireSomeUintErrorUsage.checkMul_modelBody with
  | [Stmt.requireError
        (Expr.logicalOr
          (Expr.eq (Expr.param "b") (Expr.literal 0))
          (Expr.eq
            (Expr.div (Expr.mul (Expr.param "a") (Expr.param "b")) (Expr.param "b"))
            (Expr.param "a")))
        "MulOverflow"
        [Expr.param "a", Expr.param "b"],
      Stmt.letVar "result" (Expr.mul (Expr.param "a") (Expr.param "b")),
      Stmt.return (Expr.localVar "result")] =>
      true
  | _ => false

example : checkMulLowersToTypedRequireError = true := by native_decide

def checkAddExecutableReturnsSumWhenSafe : Bool :=
  match RequireSomeUintErrorUsage.checkAdd 1 2 Verity.defaultState with
  | .success v _ => v == 3
  | .revert _ _ => false

example : checkAddExecutableReturnsSumWhenSafe = true := by native_decide

def checkAddExecutableRevertsOnOverflow : Bool :=
  let maxUint : Uint256 := Verity.Core.Uint256.ofNat Verity.Stdlib.Math.MAX_UINT256
  match RequireSomeUintErrorUsage.checkAdd maxUint 1 Verity.defaultState with
  | .revert msg _ => msg == "AddOverflow()"
  | .success _ _ => false

example : checkAddExecutableRevertsOnOverflow = true := by native_decide

end RequireSomeUintErrorSmoke

end Compiler.MacroCustomErrorFeatureTest
