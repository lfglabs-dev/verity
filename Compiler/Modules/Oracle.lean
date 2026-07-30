/- 
  Compiler.Modules.Oracle: Oracle Read Modules

  Standard ECMs for read-only oracle integrations:
  - `oracleReadUint256`: staticcall a target with ABI-encoded selector and static
    arguments, requiring exactly one 32-byte return word.

  Trust assumption: the target address implements the selected oracle read
  interface and returns one ABI-encoded `uint256` word.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Oracle

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

private def selectorHex (selector : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 selector)

private def compileStaticSingleWordRead
    (moduleName : String) (selector : Nat) (numStaticArgs : Nat)
    (resultVar : String) (args : List YulExpr) : Except String (List YulStmt) := do
    if selector >= 2^32 then
      throw s!"{moduleName}: selector {selectorHex selector} exceeds 4 bytes"
    let targetExpr ← match args.head? with
      | some target => pure target
      | none => throw s!"{moduleName} expects at least 1 argument (target)"
    let staticArgExprs := args.drop 1
    let calldataSize := 4 + numStaticArgs * 32
    let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
    let ptrName := "__oracle_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let storeSelector := YulStmt.exprStmt (YulExpr.call "mstore" [
      ptrExpr,
      YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    ])
    let storeArgs := staticArgExprs.zipIdx.map fun (argExpr, idx) =>
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + idx * 32)],
        argExpr
      ])
    let advancePtr := YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit frameSize]
    ])
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      targetExpr,
      ptrExpr, YulExpr.lit calldataSize,
      ptrExpr, YulExpr.lit 32
    ]
    let revertOnFailure := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__oracle_success"]) [
      YulStmt.let_ "__oracle_rds" (YulExpr.call "returndatasize" []),
      YulStmt.exprStmt (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__oracle_rds"
      ]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__oracle_rds"])
    ]
    let requireSingleWord := YulStmt.if_ (YulExpr.call "iszero" [
      YulExpr.call "eq" [YulExpr.call "returndatasize" [], YulExpr.lit 32]
    ]) [
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [ptrExpr])
    pure [bindResult, YulStmt.block (
      [loadPtr, storeSelector] ++ storeArgs ++ [advancePtr] ++
      [YulStmt.let_ "__oracle_success" callExpr, revertOnFailure, requireSingleWord, assignResult]
    )]

/-- Read-only oracle module that ABI-encodes `selector(staticArgs...)`, performs
    a `staticcall`, forwards revert returndata on failure, requires exactly one
    32-byte return word, and binds it to `resultVar`.

    Arguments passed to the module are `[target] ++ staticArgs`. -/
def oracleReadUint256Module (resultVar : String) (selector : Nat) (numStaticArgs : Nat) :
    ExternalCallModule where
  name := "oracleReadUint256"
  numArgs := 1 + numStaticArgs
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["oracle_read_uint256_interface"]
  summarySelector := some selector
  summaryMutability := .staticcall
  compile := fun _ctx args =>
    compileStaticSingleWordRead "oracleReadUint256" selector numStaticArgs resultVar args

/-- Typed-interface oracle summary for a view method with one static ABI-word
    return. The summary name is source-shaped, e.g. `IOracle.price`, while the
    selector records the exact ABI method selector used by the generated
    `staticcall`. -/
def typedReadWordSummaryModule
    (resultVar summaryName : String) (selector : Nat) (numStaticArgs : Nat) :
    ExternalCallModule where
  name := "oracleSummary"
  numArgs := 1 + numStaticArgs
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := [s!"oracle_summary:{summaryName}"]
  summaryName := summaryName
  summarySelector := some selector
  summaryMutability := .staticcall
  compile := fun _ctx args =>
    compileStaticSingleWordRead "oracleSummary" selector numStaticArgs resultVar args

/-- Convenience: create a `Stmt.ecm` for a read-only `uint256` oracle call. -/
def oracleReadUint256 (resultVar : String) (target : Expr) (selector : Nat) (staticArgs : List Expr) :
    Stmt :=
  .ecm (oracleReadUint256Module resultVar selector staticArgs.length) ([target] ++ staticArgs)

theorem typedReadWordSummaryModule_static
    (resultVar summaryName : String) (selector numStaticArgs : Nat) :
    (typedReadWordSummaryModule resultVar summaryName selector numStaticArgs).summaryMutability =
      .staticcall := rfl

theorem typedReadWordSummaryModule_assumption
    (resultVar summaryName : String) (selector numStaticArgs : Nat) :
    (typedReadWordSummaryModule resultVar summaryName selector numStaticArgs).axioms =
      [s!"oracle_summary:{summaryName}"] := rfl

end Compiler.Modules.Oracle
