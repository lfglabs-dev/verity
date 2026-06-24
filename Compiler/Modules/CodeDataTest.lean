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
  [ { name := "blob", ty := .tuple [.bytes32, .bytes32, .bytes32], source := .memory }
  , { name := "meta", ty := .tuple [.bytes32, .uint256], source := .calldata } ]

private def deployUsesPayloadBuffer : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "create2" [_value, .ident "__abi_frame_sstore2", .lit 160, _salt]) => true
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

-- Empty-code edge case (#1967): a CodeData payload with no fields. The
-- typed surface must still produce a well-formed `create2` deploy and
-- `extcodecopy` read so callers can use SSTORE2-style pointers as opaque
-- markers without storing any data.
private def emptyPayload := layout []

-- Short-code edge case (#1967): a one-word payload exercises the minimal
-- non-empty layout. Padding, alignment, and pointer derivation must agree
-- with the larger blob+meta payload used by the original test.
private def shortPayload := layout
  [ { name := "word", ty := .uint256, source := .memory } ]

-- Dynamic payload (#1967): `layoutSourcesSupported` must reject dynamic
-- types so callers get a clear failure mode rather than corrupt code-as-
-- data shapes.
private def dynamicPayload := layout
  [ { name := "blob", ty := .bytes, source := .memory } ]

private def dynamicStringPayload := layout
  [ { name := "message", ty := .string, source := .calldata } ]

private def dynamicArrayPayload := layout
  [ { name := "items", ty := .array .uint256, source := .calldata } ]

private def nestedDynamicPayload := layout
  [ { name := "wrapped", ty := .tuple [.uint256, .bytes], source := .calldata } ]

private def dynamicStoragePayload := layout
  [ { name := "stored", ty := .bytes, source := .storage } ]

private def deployUsesDynamicSize : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "create2" [_value, .ident "__abi_frame_dynamic", .ident "__codedata_bytes_size", _salt]) => true
    | _ => false

private def hasDynamicBytesStoresAndMemoryCopy : List YulStmt → Bool :=
  fun stmts =>
    stmts.any (fun
      | .expr (.call "mstore" [.ident "__abi_frame_dynamic", .lit 32]) => true
      | _ => false) &&
    stmts.any (fun
      | .expr (.call "mstore" [.call "add" [.ident "__abi_frame_dynamic", .lit 32], .ident "blob_length"]) => true
      | _ => false) &&
    stmts.any (fun
      | .expr (.call "mcopy" [.ident "__codedata_bytes_data_dest", .ident "blob_data_offset", .ident "blob_length"]) => true
      | _ => false)

private def hasDynamicStringCalldataCopy : List YulStmt → Bool :=
  fun stmts =>
    stmts.any fun
      | .expr (.call "calldatacopy" [.ident "__codedata_bytes_data_dest", .ident "message_data_offset", .ident "message_length"]) => true
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
  assert "trust surface is explicit" (trustSurface.length == 5)
  let returnCodeData ←
    match compileStmt [] [] [] .calldata [] false [] [] (Stmt.returnCodeData (Expr.param "ptr")) with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError err)
  assert "returnCodeData guards extcodesize before subtracting code offset"
    (returnCodeDataHasExtentGuard returnCodeData)
  -- Empty-code edge case: layout with no fields still lowers to a real
  -- create2/extcodecopy pair (#1967).
  let emptyWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := emptyPayload }
  let emptyRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 0
      size := YulExpr.lit 0
      payload := emptyPayload }
  let emptyRoundtrip ←
    match roundtripShape "emptyPtr" "empty" emptyWrite emptyRead with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"empty payload roundtrip failed: {err}")
  assert "empty-payload roundtrip emits create2 + extcodecopy"
    (hasCreate2AndExtcodecopy emptyRoundtrip)
  assert "empty-payload layout has zero head words"
    (emptyPayload.headWords == 0)
  -- Short-code edge case: single-word payload (#1967).
  let shortWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := shortPayload }
  let shortRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 0
      size := YulExpr.lit 32
      payload := shortPayload }
  let shortRoundtrip ←
    match roundtripShape "shortPtr" "short" shortWrite shortRead with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"short payload roundtrip failed: {err}")
  assert "short-payload roundtrip emits create2 + extcodecopy"
    (hasCreate2AndExtcodecopy shortRoundtrip)
  assert "short-payload layout has exactly one head word"
    (shortPayload.headWords == 1)
  -- Dynamic bytes/string payloads (#2023 part 1): CodeData accepts exactly
  -- one bytes-like field from calldata or memory and emits an ABI-compatible
  -- head offset + length + padded data payload with a runtime-sized create2.
  let dynamicWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := dynamicPayload }
  let dynamicRoundtrip ←
    match Compiler.Modules.CodeData.writeTyped "dynamicPtr" "dynamic" dynamicWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic bytes payload write failed: {err}")
  assert "dynamic bytes payload write uses runtime create2 size"
    (deployUsesDynamicSize dynamicRoundtrip)
  assert "dynamic bytes payload writes ABI head/length and copies memory bytes"
    (hasDynamicBytesStoresAndMemoryCopy dynamicRoundtrip)
  let dynamicStringWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := dynamicStringPayload }
  let dynamicStringStmts ←
    match Compiler.Modules.CodeData.writeTyped "dynamicStringPtr" "dynamic" dynamicStringWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic string payload write failed: {err}")
  assert "dynamic string payload copies calldata bytes"
    (hasDynamicStringCalldataCopy dynamicStringStmts)
  let dynamicRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 0
      size := YulExpr.ident "size"
      payload := dynamicPayload }
  let dynamicReadResult := Compiler.Modules.CodeData.readTyped dynamicRead
  assert "dynamic bytes payload read is accepted"
    (match dynamicReadResult with | .ok _ => true | .error _ => false)
  assert "dynamic payload layout flags hasDynamic"
    dynamicPayload.hasDynamic
  assert "dynamic bytes ABI constants fix head/length/data offsets"
    (codeDataBytesLengthOffset == codeDataBytesHeadOffset &&
      codeDataBytesDataOffset == codeDataBytesHeadOffset + 32 &&
      codeDataBytesPayloadBytes 33 == codeDataBytesDataOffset + codeDataBytesPaddedDataBytes 33)
  let rejectedDynamicLayouts :=
    [dynamicArrayPayload, nestedDynamicPayload, dynamicStoragePayload]
  assert "nested and broader dynamic CodeData layouts stay rejected"
    (rejectedDynamicLayouts.all fun payload =>
      match Compiler.Modules.CodeData.writeTyped "rejectedPtr" "rejected" { salt := YulExpr.ident "salt", payload } with
      | .ok _ => false
      | .error _ => true)

end Compiler.Modules.CodeDataTest
