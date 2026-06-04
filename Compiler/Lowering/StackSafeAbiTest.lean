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

end Compiler.Lowering.StackSafeAbiTest
