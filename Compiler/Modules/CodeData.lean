import Compiler.ABI.Frame
import Compiler.Modules.Create2SSTORE2

namespace Compiler.Modules.CodeData

open Compiler.ABI.Frame
open Compiler.ECM
open Compiler.Yul

structure CodeDataWrite where
  salt : YulExpr
  value : YulExpr := YulExpr.lit 0
  payload : FrameLayout
  deriving Repr

structure CodeDataRead where
  pointer : YulExpr
  destOffset : YulExpr
  codeOffset : YulExpr
  size : YulExpr
  payload : FrameLayout
  deriving Repr

def trustSurface : List String :=
  [ "CREATE2 address derivation is trusted at the EVM boundary"
  , "SSTORE2 pointer code layout is trusted as code-as-data"
  , "extcodecopy reads immutable deployed code bytes into caller-owned memory"
  , "ABI frame layout is typed by Compiler.ABI.Frame before write/read lowering"
  , "Runtime-sized dynamic ABI payload copies preserve the caller-provided byte extent" ]

def sstore2PrefixBytes : Nat := 1

def sstore2PrefixOffset : YulExpr := YulExpr.lit sstore2PrefixBytes

def sstore2RuntimeSize (payloadSize : YulExpr) : YulExpr :=
  YulExpr.call "add" [sstore2PrefixOffset, payloadSize]

def codeDataPayloadSupported (payload : FrameLayout) : Bool :=
  if layoutHasRuntimeSize payload then
    layoutRuntimeSourcesSupported payload
  else
    !payload.hasDynamic && layoutSourcesSupported payload

private def copyMemorySlice (dest src size : YulExpr) : List YulStmt :=
  [ YulStmt.for_
      [YulStmt.let_ "__codedata_copy_i" (YulExpr.lit 0)]
      (YulExpr.call "lt" [YulExpr.ident "__codedata_copy_i", size])
      [YulStmt.assign "__codedata_copy_i"
        (YulExpr.call "add" [YulExpr.ident "__codedata_copy_i", YulExpr.lit 32])]
      [YulStmt.exprStmt (YulExpr.call "mstore"
        [ YulExpr.call "add" [dest, YulExpr.ident "__codedata_copy_i"]
        , YulExpr.call "mload" [YulExpr.call "add" [src, YulExpr.ident "__codedata_copy_i"]] ])] ]

private def materializeStaticSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) := do
  let (payloadPrelude, payloadArgs) := materializePayloadToMemory (base ++ "_payload") payload
  let payloadOffset ←
    match payloadArgs with
    | [offset, _size] => pure offset
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let payloadSize ←
    match payloadArgs with
    | [_offset, size] => pure size
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let ptr := YulExpr.ident (ptrName base)
  let dest := YulExpr.call "add" [ptr, sstore2PrefixOffset]
  pure
    ( payloadPrelude ++
      [ YulStmt.let_ (ptrName base) (YulExpr.call "mload" [YulExpr.lit 64])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [ YulExpr.lit 64
          , YulExpr.call "add" [ptr, sstore2RuntimeSize payloadSize] ])
      , YulStmt.exprStmt (YulExpr.call "mstore8" [ptr, YulExpr.lit 0]) ] ++
      copyMemorySlice dest payloadOffset payloadSize
    , [ptr, sstore2RuntimeSize payloadSize] )

private def materializeDynamicSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) := do
  let (prelude, args) ← materializeRuntimePayloadToMemoryWithPrefix base sstore2PrefixBytes payload
  pure
    ( prelude ++
      [YulStmt.exprStmt (YulExpr.call "mstore8" [YulExpr.ident (ptrName base), YulExpr.lit 0])]
    , args )

def materializeSstore2Payload (base : String) (payload : FrameLayout) :
    Except String (List YulStmt × List YulExpr) :=
  if layoutHasRuntimeSize payload then
    materializeDynamicSstore2Payload base payload
  else
    materializeStaticSstore2Payload base payload

def writeTyped (resultVar base : String) (write : CodeDataWrite) : Except String (List YulStmt) := do
  if !codeDataPayloadSupported write.payload then
    throw "CodeData write payload has unsupported frame source"
  let (prelude, payloadArgs) ← materializeSstore2Payload base write.payload
  let initcodeOffset ←
    match payloadArgs with
    | [offset, _size] => pure offset
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let initcodeSize ←
    match payloadArgs with
    | [_offset, size] => pure size
    | _ => throw "CodeData write expected a memory payload pointer and size"
  let deploy ← (Compiler.Modules.Create2SSTORE2.deployModule resultVar).compile {}
    [write.value, initcodeOffset, initcodeSize, write.salt]
  pure (prelude ++ deploy)

def readTyped (read : CodeDataRead) : Except String (List YulStmt) := do
  if !codeDataPayloadSupported read.payload then
    throw "CodeData read payload has unsupported frame source"
  (Compiler.Modules.Create2SSTORE2.readCodeModule).compile {}
    [read.pointer, read.destOffset, read.codeOffset, read.size]

def roundtripShape (resultVar base : String) (write : CodeDataWrite) (read : CodeDataRead) :
    Except String (List YulStmt) := do
  let w ← writeTyped resultVar base write
  let r ← readTyped read
  pure (w ++ r)

def hasCreate2AndExtcodecopy (stmts : List YulStmt) : Bool :=
  let hasCreate2 := stmts.any fun
    | .let_ _ (.call "create2" _) => true
    | _ => false
  let hasExtcodecopy := stmts.any fun
    | .exprStmt (.call "extcodecopy" _) => true
    | _ => false
  hasCreate2 && hasExtcodecopy

end Compiler.Modules.CodeData
