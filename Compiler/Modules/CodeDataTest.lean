import Compiler.Modules.CodeData
import Compiler.CompilationModel.Compile

namespace Compiler.Modules.CodeDataTest

open Compiler.ABI.Frame
open Compiler.CompilationModel
open Compiler.Modules.CodeData
open Compiler.Yul

private def assert (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"CodeData test failed: {label}")
  IO.println s!"ok: {label}"

private def payload := layout
  [ { name := "blob", ty := .bytes, source := .memory, tailBytes := 96 }
  , { name := "meta", ty := .tuple [.bytes32, .uint256], source := .calldata } ]

private def deployUsesPayloadBuffer : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "create2" [_value, .ident "__abi_frame_sstore2", .lit 192, _salt]) => true
    | _ => false

private def returnCodeDataHasExtentGuard : List YulStmt → Bool
  | [YulStmt.block stmts] =>
      stmts.any fun stmt =>
        match stmt with
        | YulStmt.if_
            (.call "iszero" [
              .call "gt" [
                .ident "__return_code_extent",
                .ident "__return_code_offset"
              ]
            ])
            [YulStmt.expr (.call "revert" [.lit 0, .lit 0])] => true
        | _ => false
  | _ => false

#eval! do
  let write : CodeDataWrite :=
    { salt := YulExpr.ident "salt"
      payload }
  let read : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 1
      size := YulExpr.ident "size"
      payload }
  let roundtrip ←
    match roundtripShape "storedPtr" "sstore2" write read with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError err)
  assert "typed roundtrip has create2 and extcodecopy" (hasCreate2AndExtcodecopy roundtrip)
  assert "typed write deploys the materialized payload buffer" (deployUsesPayloadBuffer roundtrip)
  assert "trust surface is explicit" (trustSurface.length == 4)
  let returnCodeData ←
    match compileStmt [] [] [] .calldata [] false [] [] (Stmt.returnCodeData (Expr.param "ptr")) with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError err)
  assert "returnCodeData guards extcodesize before subtracting code offset"
    (returnCodeDataHasExtentGuard returnCodeData)

end Compiler.Modules.CodeDataTest
