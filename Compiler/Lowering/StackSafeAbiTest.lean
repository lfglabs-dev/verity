import Compiler.Lowering.StackSafeAbi

namespace Compiler.Lowering.StackSafeAbiTest

open Compiler.ABI.Frame
open Compiler.CompilationModel
open Compiler.Lowering.StackSafeAbi
open Compiler.Yul

private def assert (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"stack safe ABI test failed: {label}")
  IO.println s!"ok: {label}"

private def bigDynamicPayload : List FrameField :=
  [ { name := "toId", ty := .bytes32, source := .calldata }
  , { name := "toMarket", ty := .tuple [.address, .uint256, .uint256, .address], source := .calldata }
  , { name := "takes", ty := .array (.tuple [.address, .uint256, .bytes]), source := .calldata } ]

private def smallStaticPayload : List FrameField :=
  [ { name := "id", ty := .bytes32, source := .calldata }
  , { name := "amount", ty := .uint256, source := .calldata } ]

private def countMstores : List YulStmt → Nat :=
  List.length ∘ List.filter (fun stmt =>
    match stmt with
    | .expr (.call "mstore" _) => true
    | _ => false)

private def returnsBytes (bytes : Nat) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .expr (.call "return" [.lit 0, .lit n]) => n == bytes
    | _ => false

private def callsWithInputBytes (bytes : Nat) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "call" [_gas, _target, _value, .lit 0, .lit n, _out, _outSize]) => n == bytes
    | _ => false

private def logsWithDataBytes (bytes : Nat) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .expr (.call "log1" [.lit 0, .lit n, .lit topic]) => n == bytes && topic != 0
    | _ => false

#eval! do
  match lowerEvent "Take" bigDynamicPayload with
  | .ok ev => assert "event lowering uses memory pointer" (usesPointerAbi ev)
  | .error err => throw (IO.userError err)
  match lowerExternalCall "callback" (YulExpr.ident "target") (YulExpr.lit 0) bigDynamicPayload with
  | .ok call => assert "external-call lowering uses memory pointer" (usesPointerAbi call)
  | .error err => throw (IO.userError err)
  match lowerDynamicReturn "dynamicReturn" bigDynamicPayload with
  | .ok ret => assert "dynamic return lowering uses memory pointer" (usesPointerAbi ret)
  | .error err => throw (IO.userError err)
  match lowerFrameSpilled "toMarket" bigDynamicPayload with
  | .ok lowered => assert "frame-spilled lowering allocates memory early" (!lowered.prologue.isEmpty && lowered.args.length == 2)
  | .error err => throw (IO.userError err)
  match lowerEvent "SmallStatic" smallStaticPayload with
  | .ok ev =>
      assert "inline event lowering stores payload" (countMstores ev == 2)
      assert "inline event lowering logs payload bytes" (logsWithDataBytes 64 ev)
  | .error err => throw (IO.userError err)
  match lowerExternalCall "smallCallback" (YulExpr.ident "target") (YulExpr.lit 0) smallStaticPayload with
  | .ok call =>
      assert "inline external-call lowering stores payload" (countMstores call == 2)
      assert "inline external-call lowering passes payload bytes" (callsWithInputBytes 64 call)
  | .error err => throw (IO.userError err)
  match lowerDynamicReturn "smallReturn" smallStaticPayload with
  | .ok ret =>
      assert "inline dynamic return lowering stores payload" (countMstores ret == 2)
      assert "inline dynamic return lowering returns payload bytes" (returnsBytes 64 ret)
  | .error err => throw (IO.userError err)

end Compiler.Lowering.StackSafeAbiTest
