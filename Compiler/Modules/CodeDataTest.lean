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
    | .let_ _ (.call "create2"
        [ _value
        , .ident "__abi_frame_sstore2"
        , .call "add" [.lit 1, .lit 160]
        , _salt ]) => true
    | _ => false

private def writesSstore2Prefix (base : String) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .exprStmt (.call "mstore8" [.ident ptr, .lit 0]) => ptr == ptrName base
    | _ => false

private def readSkipsSstore2Prefix : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .exprStmt (.call "extcodecopy" [_ptr, _dest, .lit 1, _size]) => true
    | _ => false

private def deployUsesRuntimeSize (base sizeName : String) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "create2"
        [ _value
        , .ident ptr
        , .call "add" [.lit 1, .ident size]
        , _salt ]) =>
          ptr == ptrName base && size == sizeName
    | _ => false

private def copiesRuntimeMemoryPayload (sourceName sizeName : String) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .for_ _ (.call "lt" [.ident "__abi_frame_copy_i", .ident size]) _ body =>
        size == sizeName &&
          body.any (fun bodyStmt =>
            match bodyStmt with
            | .exprStmt (.call "mstore"
                [ _
                , .call "mload" [.call "add" [.ident source, .ident "__abi_frame_copy_i"]] ]) =>
                  source == sourceName
            | _ => false)
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
            [YulStmt.exprStmt (.call "revert" [.lit 0, .lit 0])] => true
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

-- Dynamic CodeData payload (#2023): callers can pass a pre-encoded
-- runtime-sized ABI payload such as `abi.encode(market)`. The ParamType stays
-- attached to the frame for typed read/write/return/id reasoning, while the
-- byte extent is supplied by the caller at runtime.
private def dynamicPayload := runtimeSizedLayout
  [ { name := "market", ty := .tuple [.address, .address, .bytes], source := .memory, sourceBase := "marketAbi" } ]
  (YulExpr.ident "marketSize")

private def dynamicBytesPayload := layout
  [ { name := "blob", ty := .bytes, source := .memory } ]

private def dynamicStringPayload := layout
  [ { name := "message", ty := .string, source := .calldata } ]

private def dynamicArrayPayload := layout
  [ { name := "items", ty := .array .uint256, source := .calldata } ]

private def nestedDynamicPayload := layout
  [ { name := "wrapped", ty := .tuple [.uint256, .bytes], source := .calldata } ]

private def dynamicStoragePayload := layout
  [ { name := "stored", ty := .bytes, source := .storage } ]

private def deployUsesGeneratedDynamicSize (base : String) : List YulStmt → Bool :=
  fun stmts => stmts.any fun stmt =>
    match stmt with
    | .let_ _ (.call "create2"
        [ _value
        , .ident ptr
        , .ident "__codedata_bytes_total_size"
        , _salt ]) =>
          ptr == ptrName base
    | _ => false

private def hasGeneratedDynamicBytesStoresAndMemoryCopy (base : String) : List YulStmt → Bool :=
  fun stmts =>
    let payloadBase := YulExpr.call "add" [YulExpr.ident (ptrName base), YulExpr.lit 1]
    stmts.any (fun
      | .exprStmt (.call "mstore" [actualBase, .lit 32]) => actualBase == payloadBase
      | _ => false) &&
    stmts.any (fun
      | .exprStmt (.call "mstore" [.call "add" [actualBase, .lit 32], .ident "blob_length"]) =>
          actualBase == payloadBase
      | _ => false) &&
    stmts.any (fun
      | .exprStmt (.call "mcopy" [.ident "__codedata_bytes_data_dest", .ident "blob_data_offset", .ident "blob_length"]) => true
      | _ => false)

private def hasGeneratedDynamicStringCalldataCopy : List YulStmt → Bool :=
  fun stmts =>
    stmts.any fun
      | .exprStmt (.call "calldatacopy" [.ident "__codedata_bytes_data_dest", .ident "message_data_offset", .ident "message_length"]) => true
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
  assert "typed write materializes observable SSTORE2 STOP prefix"
    (writesSstore2Prefix "sstore2" roundtrip)
  assert "typed read skips observable SSTORE2 prefix byte"
    (readSkipsSstore2Prefix roundtrip)
  assert "trust surface is explicit" (trustSurface.length == 6)
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
  -- Dynamic runtime-sized payload (#2023): typed CodeData accepts a
  -- pre-encoded ABI payload, stores `STOP ++ payload`, and uses the caller's
  -- runtime byte length for the CREATE2 slice.
  let dynamicWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := dynamicPayload }
  let dynamicRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 1
      size := YulExpr.ident "marketSize"
      payload := dynamicPayload }
  let dynamicRoundtrip ←
    match roundtripShape "dynamicPtr" "dynamic" dynamicWrite dynamicRead with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic payload roundtrip failed: {err}")
  assert "dynamic CodeData roundtrip emits create2 + extcodecopy"
    (hasCreate2AndExtcodecopy dynamicRoundtrip)
  assert "dynamic CodeData writes SSTORE2 prefix"
    (writesSstore2Prefix "dynamic" dynamicRoundtrip)
  assert "dynamic CodeData create2 uses runtime payload size plus prefix"
    (deployUsesRuntimeSize "dynamic" "marketSize" dynamicRoundtrip)
  assert "dynamic CodeData copies the runtime-sized ABI payload"
    (copiesRuntimeMemoryPayload "marketAbi" "marketSize" dynamicRoundtrip)
  assert "dynamic CodeData read skips SSTORE2 prefix"
    (readSkipsSstore2Prefix dynamicRoundtrip)
  assert "dynamic payload layout flags hasDynamic"
    dynamicPayload.hasDynamic
  assert "dynamic payload layout records runtime byte size"
    (layoutHasRuntimeSize dynamicPayload)
  -- Dynamic bytes/string payloads (#2023): CodeData can also build the ABI
  -- bytes/string payload at runtime from typed calldata/memory sources.
  let dynamicBytesWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := dynamicBytesPayload }
  let dynamicBytesStmts ←
    match Compiler.Modules.CodeData.writeTyped "dynamicBytesPtr" "dynamicBytes" dynamicBytesWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic bytes payload write failed: {err}")
  assert "dynamic bytes payload write uses generated runtime create2 size"
    (deployUsesGeneratedDynamicSize "dynamicBytes" dynamicBytesStmts)
  assert "dynamic bytes payload writes SSTORE2 prefix"
    (writesSstore2Prefix "dynamicBytes" dynamicBytesStmts)
  assert "dynamic bytes payload writes ABI head/length and copies memory bytes"
    (hasGeneratedDynamicBytesStoresAndMemoryCopy "dynamicBytes" dynamicBytesStmts)
  let dynamicStringWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := dynamicStringPayload }
  let dynamicStringStmts ←
    match Compiler.Modules.CodeData.writeTyped "dynamicStringPtr" "dynamicString" dynamicStringWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic string payload write failed: {err}")
  assert "dynamic string payload copies calldata bytes"
    (hasGeneratedDynamicStringCalldataCopy dynamicStringStmts)
  let dynamicBytesRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 1
      size := YulExpr.ident "size"
      payload := dynamicBytesPayload }
  assert "dynamic bytes payload read is accepted"
    (match Compiler.Modules.CodeData.readTyped dynamicBytesRead with | .ok _ => true | .error _ => false)
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
