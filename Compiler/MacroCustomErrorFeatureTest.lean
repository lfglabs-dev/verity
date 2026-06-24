import Compiler.CompilationModel
import Compiler.Yul.PrettyPrint
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

namespace MacroPanicUsageSmoke

verity_contract MacroPanicUsage where
  storage
    sentinel : Uint256 := slot 0

  function failWithLiteralPanic () : Unit := do
    panic(0x11)

  function failWithParamPanic (code : Uint256) : Unit := do
    panic(code)

def literalPanicModelUsesBuiltInPanic : Bool :=
  match MacroPanicUsage.failWithLiteralPanic_modelBody with
  | [Stmt.panicCode (Expr.literal 0x11), Stmt.stop] => true
  | _ => false

example : literalPanicModelUsesBuiltInPanic = true := by native_decide

def paramPanicModelUsesBuiltInPanic : Bool :=
  match MacroPanicUsage.failWithParamPanic_modelBody with
  | [Stmt.panicCode (Expr.param "code"), Stmt.stop] => true
  | _ => false

example : paramPanicModelUsesBuiltInPanic = true := by native_decide

def literalPanicExecutableReverts : Bool :=
  match MacroPanicUsage.failWithLiteralPanic Verity.defaultState with
  | .revert _ state => state.sender == Verity.defaultState.sender
  | .success _ _ => false

example : literalPanicExecutableReverts = true := by native_decide

def panicYulPayloadObservable : Bool :=
  let contract : CompilationModel :=
    { name := "PanicSurface"
      fields := []
      functions := [
        { name := "boom"
          params := []
          returnType := none
          body := [Stmt.panicCode (Expr.literal 0x11)] }
      ] }
  match compileContract contract with
  | Except.ok ir =>
      let yul := Compiler.Yul.prettyStmts (ir.functions.find? (·.name == "boom") |>.map (·.body) |>.getD [])
      yul.contains "mstore(0, shl(224, 0x4e487b71))" &&
        yul.contains "mstore(4, 17)" &&
        yul.contains "revert(0, 36)"
  | Except.error _ => false

example : panicYulPayloadObservable = true := by native_decide

end MacroPanicUsageSmoke

namespace MacroCustomErrorRuntimeArgSmoke

verity_contract MacroCustomErrorRuntimeArgs where
  storage
    sentinel : Uint256 := slot 0

  errors
    error ExecutionResult(Uint256, Uint256, Address, Bool)

  function failRuntime (preOpGas : Uint256, paid : Uint256, target : Address, success : Bool) : Unit := do
    let total := add preOpGas paid
    revertError ExecutionResult(total, add paid 1, target, success)

def failRuntimeModelUsesRuntimeCustomErrorArgs : Bool :=
  match MacroCustomErrorRuntimeArgs.failRuntime_modelBody with
  | [Stmt.letVar "total" (Expr.add (Expr.param "preOpGas") (Expr.param "paid")),
      Stmt.revertError "ExecutionResult"
        [Expr.localVar "total",
          Expr.add (Expr.param "paid") (Expr.literal 1),
          Expr.param "target",
          Expr.param "success"],
      Stmt.stop] =>
      true
  | _ => false

example : failRuntimeModelUsesRuntimeCustomErrorArgs = true := by decide

def failRuntimeExecutableUsesRuntimeFallback : Bool :=
  match MacroCustomErrorRuntimeArgs.failRuntime 3 4 9 true Verity.defaultState with
  | .revert msg state =>
      msg == "ExecutionResult(7, 5, 9, true)" &&
        state.sender == Verity.defaultState.sender
  | .success _ _ => false

example : failRuntimeExecutableUsesRuntimeFallback = true := by decide

end MacroCustomErrorRuntimeArgSmoke

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

/--
error: unknown custom error 'MissingOverflow'
-/
#guard_msgs in
verity_contract RequireSomeUintErrorUnknownErrorRejected where
  storage
  errors
    error AddOverflow ()

  function bad (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeAdd a b) MissingOverflow()
    return result

/--
error: custom error 'MulOverflow' expects 2 args, got 1
-/
#guard_msgs in
verity_contract RequireSomeUintErrorWrongArityRejected where
  storage
  errors
    error MulOverflow (Uint256, Uint256)

  function bad (a : Uint256, b : Uint256) : Uint256 := do
    let result ← requireSomeUintError (safeMul a b) MulOverflow(a)
    return result

/--
error: custom error 'NeedsAmount' arg 1 in function 'bad' expects Verity.Macro.ValueType.uint256, got Verity.Macro.ValueType.bool
-/
#guard_msgs in
verity_contract CustomErrorWrongArgTypeRejected where
  storage
  errors
    error NeedsAmount (Uint256)

  function bad (ok : Bool) : Unit := do
    revertError NeedsAmount(ok)

/--
error: unsupported requireSomeUintError source; expected safeAdd, safeSub, safeMul, or safeDiv
-/
#guard_msgs in
verity_contract RequireSomeUintErrorInvalidSourceRejected where
  storage
  errors
    error AddOverflow ()

  function bad (a : Uint256) : Uint256 := do
    let result ← requireSomeUintError a AddOverflow()
    return result

end Compiler.MacroCustomErrorFeatureTest
