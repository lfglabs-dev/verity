import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Model.Denote

namespace Compiler.Proofs.IRGeneration.SourceSemanticsFeatureTest

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration

private def storageArraySourceSpec : CompilationModel :=
  { name := "StorageArraySource"
    fields := [{ name := "queue", ty := .dynamicArray .uint256, «slot» := some 7 }]
    constructor := none
    functions :=
      [ { name := "length"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayLength "queue")] }
      , { name := "first"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayElement "queue" (.literal 0))] }
      , { name := "push"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.storageArrayPush "queue" (.param "value"), .stop] }
      , { name := "write0"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.setStorageArrayElement "queue" (.literal 0) (.param "value"), .stop] }
      , { name := "pop"
          params := []
          returnType := none
          body := [Stmt.storageArrayPop "queue", .stop] } ] }

private def storageArrayInitialWorld : Verity.ContractState :=
  Verity.defaultState.writeArray 7 [11, 17]

private def signedScalarSourceSpec : CompilationModel :=
  { name := "SignedScalarSource"
    fields := []
    constructor := none
    functions :=
      [ { name := "echoSigned"
          params := [{ name := "x", ty := .int256 }]
          returnType := none
          returns := [.int256]
          body := [Stmt.return (Expr.param "x")] } ] }

private def emitSourceSpec : CompilationModel :=
  { name := "EmitSource"
    fields := []
    events := [{ name := "Ping", params := [{ name := "value", ty := .uint256, kind := .unindexed }] }]
    constructor := none
    functions :=
      [ { name := "emitPing"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.emit "Ping" [Expr.param "value"], .stop] } ] }

private def indexedEmitSourceSpec : CompilationModel :=
  { name := "IndexedEmitSource"
    fields := []
    events := [
      { name := "Ping"
        params := [
          { name := "topic", ty := .uint256, kind := .indexed },
          { name := "value", ty := .uint256, kind := .unindexed }
        ] }
    ]
    constructor := none
    functions :=
      [ { name := "emitPing"
          params := [
            { name := "topic", ty := .uint256 },
            { name := "value", ty := .uint256 }
          ]
          returnType := none
          body := [Stmt.emit "Ping" [Expr.param "topic", Expr.param "value"], .stop] } ] }

private def storageWordFields : List Field :=
  [{ name := "root", ty := .uint256, «slot» := some 10 }]

private def storageWordAliasFields : List Field :=
  [{ name := "root", ty := .uint256, «slot» := some 10, aliasSlots := [20] }]

private def storageWordSpec : CompilationModel :=
  { name := "StorageWordSource"
    fields := storageWordFields
    constructor := none
    functions := [] }

private def storageWordState : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState, bindings := [] }

private def helperKeccakOffset : FunctionSpec :=
  { name := "hashOffset"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.literal 64)] }

private def helperKeccakSize : FunctionSpec :=
  { name := "hashSize"
    params := []
    returnType := some .uint256
    isInternal := true
    body := [Stmt.return (.literal 32)] }

private def helperKeccakSpec : CompilationModel :=
  { name := "HelperKeccak"
    fields := []
    constructor := none
    functions := [helperKeccakOffset, helperKeccakSize] }

private def helperKeccakWorld : Verity.ContractState :=
  { Verity.defaultState with
    memory := fun offset => if offset = 64 then 0x1234 else 0 }

private def helperKeccakState : SourceSemantics.RuntimeState :=
  { world := helperKeccakWorld, bindings := [] }

private def resultStorageAt? (slot : Nat) : SourceSemantics.StmtResult → Option Nat
  | .continue st => some (st.world.storage slot).val
  | .stop st => some (st.world.storage slot).val
  | .return _ st => some (st.world.storage slot).val
  | .revert => none

private def resultStorageAddrAt? (slot : Nat) : SourceSemantics.StmtResult → Option Verity.Address
  | .continue st => some (st.world.storageAddr slot)
  | .stop st => some (st.world.storageAddr slot)
  | .return _ st => some (st.world.storageAddr slot)
  | .revert => none

example :
    (sourceContractSemantics simpleStorageSupportedSpecModel [0x2e64cec1]
      { sender := 7, functionSelector := 0x2e64cec1, args := [] }
      Verity.defaultState).success = true := by
  native_decide

example :
    (sourceContractSemantics counterSupportedSpecModel
      [0xa87d942c]
      { sender := 9, functionSelector := 0xa87d942c, args := [] }
      Verity.defaultState).returnValue = some 42 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x11111111, args := [] }
      storageArrayInitialWorld).returnValue = some 2 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      storageArrayInitialWorld).returnValue = some 11 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x33333333, args := [23] }
      storageArrayInitialWorld).finalStorage 7 = 3 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x44444444, args := [29] }
      storageArrayInitialWorld).success = true := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      storageArrayInitialWorld).finalStorage 7 = 1 := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x22222222, args := [] }
      Verity.defaultState).success = false := by
  native_decide

example :
    (sourceContractSemantics storageArraySourceSpec
      [0x11111111, 0x22222222, 0x33333333, 0x44444444, 0x55555555]
      { sender := 9, functionSelector := 0x55555555, args := [] }
      Verity.defaultState).success = false := by
  native_decide

example :
    SourceSemantics.decodeSupportedParamWord .int256 (2 ^ 256 - 1) = some (2 ^ 256 - 1) := by
  native_decide

example :
    (sourceContractSemantics signedScalarSourceSpec
      [0xabcdef01]
      { sender := 9, functionSelector := 0xabcdef01, args := [2 ^ 256 - 1] }
      Verity.defaultState).returnValue = some (2 ^ 256 - 1) := by
  native_decide

example :
    (sourceContractSemantics emitSourceSpec
      [0x13572468]
      { sender := 9, functionSelector := 0x13572468, args := [77] }
      Verity.defaultState).success = true := by
  native_decide

example :
    (sourceContractSemantics indexedEmitSourceSpec
      [0x24681357]
      { sender := 9, functionSelector := 0x24681357, args := [11, 22] }
      Verity.defaultState).events =
        SourceSemantics.encodeEvents
          [{ name := "Ping"
             args := [Verity.Core.Uint256.ofNat (22 % Compiler.Constants.evmModulus)]
             indexedArgs := [
               SourceSemantics.eventSignatureTopic
                 { name := "Ping"
                   params := [
                     { name := "topic", ty := .uint256, kind := .indexed },
                     { name := "value", ty := .uint256, kind := .unindexed }
                   ] },
               Verity.Core.Uint256.ofNat (11 % Compiler.Constants.evmModulus)] }] := by
  native_decide

example :
    SourceSemantics.evalExprWithHelpers helperKeccakSpec [] 1 helperKeccakState
      (Expr.keccak256
        (Expr.internalCall "hashOffset" [])
        (Expr.internalCall "hashSize" [])) =
      some (SourceSemantics.keccakMemorySlice helperKeccakWorld.memory 64 32) := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmtWithEvents storageWordFields [] storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAddrAt? 12
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) =
        some (Verity.wordToAddress (99 : Verity.Uint256)) := by
  native_decide

example :
    resultStorageAt? 12
      (SourceSemantics.execStmtWithHelpers storageWordSpec storageWordFields 1 storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAt? 10
      (SourceSemantics.execStmt storageWordFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 0 := by
  native_decide

example :
    resultStorageAt? 22
      (SourceSemantics.execStmt storageWordAliasFields storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) = some 99 := by
  native_decide

example :
    resultStorageAddrAt? 22
      (SourceSemantics.execStmtWithEvents storageWordAliasFields [] storageWordState
        (Stmt.setStorageWord "root" 2 (.literal 99))) =
        some (Verity.wordToAddress (99 : Verity.Uint256)) := by
  native_decide

/-- Custom-error guards and payloads use the broad call-surface gate. -/
example :
    stmtTouchesUnsupportedCallSurface
      (.requireError (.externalCall "oracle" []) "OracleFailed" []) = true := by
  native_decide

example :
    stmtTouchesUnsupportedCallSurface
      (.requireError (.literal 0) "OracleFailed" [.externalCall "oracle" []]) = true := by
  native_decide

example :
    stmtTouchesUnsupportedCallSurface
      (.revertError "OracleFailed" [.internalCall "helper" []]) = true := by
  native_decide

example :
    stmtTouchesUnsupportedCallSurface
      (.requireError (.literal 0) "CallFree" [.literal 1]) = false := by
  native_decide

/-- In the no-call fragment, EIP-211 makes `revertReturndata` exactly the
empty revert admitted by the generic step proof. -/
example :
    exprTouchesUnsupportedCoreSurface .returndataSize = false := by
  native_decide

example :
    stmtTouchesUnsupportedCallSurface .revertReturndata = false := by
  native_decide

example :
    stmtTouchesUnsupportedLowLevelSurface .revertReturndata = false := by
  native_decide

example :
    stmtTouchesUnsupportedForeignSurface .revertReturndata = false := by
  native_decide

/-- Typed-error guards and payloads remain behind the constructor raw-calldata gate. -/
example :
    stmtTouchesUnsupportedConstructorRawCalldataSurface
      (.requireError .calldatasize "RawCalldata" []) = true := by
  native_decide

example :
    stmtTouchesUnsupportedConstructorRawCalldataSurface
      (.revertError "RawCalldata" [.calldataload (.literal 0)]) = true := by
  native_decide

/-- Helper-aware typed-error expressions are classified as helper-executing. -/
example :
    stmtTouchesExprInternalHelperSurface
      (.requireError (.internalCall "helper" []) "HelperFailed" []) = true := by
  native_decide

example :
    stmtTouchesExprInternalHelperSurface
      (.revertError "HelperFailed" [.internalCall "helper" []]) = true := by
  native_decide

/-- Regression: extcodesize normalises its operand to 160-bit address width.
    `extcodesize(2^160 + 1)` must query address 1, not key `2^160 + 1`. -/
example :
    SourceSemantics.evalExpr [] { world := Verity.defaultState, bindings := [] }
      (.extcodesize (.literal (2 ^ 160 + 1))) =
    some (Verity.defaultState.codeSize 1).val := by
  native_decide

/-- Regression: IR evaluator normalises extcodesize operand to 160 bits. -/
example :
    evalIRCall (IRState.initial 0) "extcodesize" [Compiler.Yul.YulExpr.lit (2 ^ 160 + 1)] =
    some ((IRState.initial 0).codeSize 1) := by
  native_decide

/-- Regression (#2397): the reserved `exp` builtin lane must reduce modulo
    2^256 at every step. A full-domain uint256 exponent (here 2^256 - 1) may
    not materialise `Nat.pow` before reducing, or the evaluator hangs. -/
example :
    SourceSemantics.evalExpr [] { world := Verity.defaultState, bindings := [] }
      (.externalCall builtinExpName [.literal 3, .literal (2 ^ 256 - 1)]) =
    some 77194726158210796949047323339125271902179989777093709359638389338608753093291 := by
  native_decide

/-- Regression (#2397): the modular exponentiation stays faithful to
    `Uint256.pow` on exponents past the 256-bit reduction boundary
    (3 ^ 300 already wraps mod 2^256). -/
example :
    SourceSemantics.evalExpr [] { world := Verity.defaultState, bindings := [] }
      (.externalCall builtinExpName [.literal 3, .literal 300]) =
    some 87572657677406793603303376128395605907379627424338442757698266976936051615345 := by
  native_decide

/-- Regression (#2397): the helper-aware evaluator shares the incremental
    modular exponentiation, so the lane stays executable over its full input
    domain there too. -/
example :
    SourceSemantics.evalExprWithHelpers storageArraySourceSpec [] 1
      { world := Verity.defaultState, bindings := [] }
      (.externalCall builtinExpName [.literal 3, .literal (2 ^ 256 - 1)]) =
    some 77194726158210796949047323339125271902179989777093709359638389338608753093291 := by
  native_decide

/-- Regression (#2397): the denotation evaluates the same lane without an
    oracle round-trip and with the same incremental modular reduction. -/
private def expLaneDenoteOracle : Compiler.CompilationModel.Denote.DenoteOracle :=
  { mappingSlot := fun _ _ => 0
    keccakMemorySlice := fun _ _ _ => 0 }

example :
    Compiler.CompilationModel.Denote.evalExpr expLaneDenoteOracle []
      { world := Verity.defaultState, bindings := [] }
      (.externalCall builtinExpName [.literal 3, .literal (2 ^ 256 - 1)]) =
    some 77194726158210796949047323339125271902179989777093709359638389338608753093291 := by
  native_decide

private def oracleSuccess42 : Nat → SourceSemantics.ExternalCallOutcome :=
  fun _ => ⟨true, [42]⟩

private def oracleFail : Nat → SourceSemantics.ExternalCallOutcome :=
  fun _ => ⟨false, []⟩

private def oracleSuccess99 : Nat → SourceSemantics.ExternalCallOutcome :=
  fun _ => ⟨true, [99]⟩

private def oracleFail0 : Nat → SourceSemantics.ExternalCallOutcome :=
  fun _ => ⟨false, [0]⟩

private def oracleIndexed : Nat → SourceSemantics.ExternalCallOutcome :=
  fun n => if n == 0 then ⟨true, [7]⟩ else ⟨false, []⟩

private def mkState (bindings : List (String × Nat))
    (oracle : Nat → SourceSemantics.ExternalCallOutcome := fun _ => ⟨false, []⟩)
    (callIdx : Nat := 0) : SourceSemantics.RuntimeState :=
  { world := Verity.defaultState, bindings, externalCallOracle := oracle,
    externalCallIndex := callIdx }

private def resultBindings (r : SourceSemantics.StmtResult) : Option (List (String × Nat)) :=
  match r with | .continue s => some s.bindings | _ => none

private def resultCallIndex (r : SourceSemantics.StmtResult) : Option Nat :=
  match r with | .continue s => some s.externalCallIndex | _ => none

private def isRevert (r : SourceSemantics.StmtResult) : Bool :=
  match r with | .revert => true | _ => false

private def isContinue (r : SourceSemantics.StmtResult) : Bool :=
  match r with | .continue _ => true | _ => false

/-- externalCallBind: oracle returns success → bindings updated, call index incremented -/
example :
    resultBindings (SourceSemantics.execStmt [] (mkState [("x", 0)] oracleSuccess42)
      (.externalCallBind ["x"] "transfer" [.literal 100])) = some [("x", 42)] := by
  native_decide

example :
    resultCallIndex (SourceSemantics.execStmt [] (mkState [("x", 0)] oracleSuccess42)
      (.externalCallBind ["x"] "transfer" [.literal 100])) = some 1 := by
  native_decide

/-- externalCallBind: oracle returns failure → revert -/
example :
    isRevert (SourceSemantics.execStmt [] (mkState [("x", 0)] oracleFail)
      (.externalCallBind ["x"] "transfer" [.literal 100])) = true := by
  native_decide

/-- tryExternalCallBind: oracle returns success → successVar=1, bindings updated -/
example :
    resultBindings (SourceSemantics.execStmt [] (mkState [("ok", 0), ("result", 0)] oracleSuccess99)
      (.tryExternalCallBind "ok" ["result"] "safecall" [.literal 50])) =
    some [("result", 99), ("ok", 1)] := by
  native_decide

example :
    resultCallIndex (SourceSemantics.execStmt [] (mkState [("ok", 0), ("result", 0)] oracleSuccess99)
      (.tryExternalCallBind "ok" ["result"] "safecall" [.literal 50])) = some 1 := by
  native_decide

/-- tryExternalCallBind: oracle returns failure → successVar=0, no revert -/
example :
    resultBindings (SourceSemantics.execStmt [] (mkState [("ok", 0), ("result", 0)] oracleFail0)
      (.tryExternalCallBind "ok" ["result"] "safecall" [.literal 50])) =
    some [("result", 0), ("ok", 0)] := by
  native_decide

example :
    isContinue (SourceSemantics.execStmt [] (mkState [("ok", 0), ("result", 0)] oracleFail0)
      (.tryExternalCallBind "ok" ["result"] "safecall" [.literal 50])) = true := by
  native_decide

/-- externalCallBind with no args and oracle keyed on call index -/
example :
    resultBindings (SourceSemantics.execStmtWithEvents [] [] (mkState [("v", 0)] oracleIndexed)
      (.externalCallBind ["v"] "ping" [])) = some [("v", 7)] := by
  native_decide

example :
    resultCallIndex (SourceSemantics.execStmtWithEvents [] [] (mkState [("v", 0)] oracleIndexed)
      (.externalCallBind ["v"] "ping" [])) = some 1 := by
  native_decide

/-- Surface gates: externalCallBind with literal args is now admitted by call/foreign/lowLevel. -/
example :
    stmtTouchesUnsupportedCallSurface
      (.externalCallBind ["x"] "transfer" [.literal 100]) = false := by
  native_decide

example :
    stmtTouchesUnsupportedForeignSurface
      (.externalCallBind ["x"] "transfer" [.literal 100]) = false := by
  native_decide

example :
    stmtTouchesUnsupportedLowLevelSurface
      (.externalCallBind ["x"] "transfer" [.literal 100]) = false := by
  native_decide

/-- Surface gates: tryExternalCallBind with literal args is similarly admitted. -/
example :
    stmtTouchesUnsupportedCallSurface
      (.tryExternalCallBind "ok" ["x"] "safecall" [.literal 50]) = false := by
  native_decide

example :
    stmtTouchesUnsupportedForeignSurface
      (.tryExternalCallBind "ok" ["x"] "safecall" [.literal 50]) = false := by
  native_decide

/-- Surface gates: call-surface args still trigger when sub-exprs touch surfaces. -/
example :
    stmtTouchesUnsupportedCallSurface
      (.externalCallBind ["x"] "transfer" [.externalCall "oracle" []]) = true := by
  native_decide

/-- Helper surface: externalCallBind with helper-free args is helper-surface-closed. -/
example :
    stmtTouchesUnsupportedHelperSurface
      (.externalCallBind ["x"] "transfer" [.literal 100]) = false := by
  native_decide

/-- Effect surface: externalCallBind remains blocked by the effect surface. -/
example :
    stmtTouchesUnsupportedEffectSurface
      (.externalCallBind ["x"] "transfer" [.literal 100]) = true := by
  native_decide

end Compiler.Proofs.IRGeneration.SourceSemanticsFeatureTest
