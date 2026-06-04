import Compiler.Modules.CodeData

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
  [ { name := "blob", ty := .bytes, source := .memory }
  , { name := "meta", ty := .tuple [.bytes32, .uint256], source := .calldata } ]

#eval! do
  let write : CodeDataWrite :=
    { salt := YulExpr.ident "salt"
      initcodeOffset := YulExpr.ident "init"
      initcodeSize := YulExpr.ident "size"
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
  assert "trust surface is explicit" (trustSurface.length == 4)

end Compiler.Modules.CodeDataTest
