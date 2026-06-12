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
  , "ABI frame layout is typed by Compiler.ABI.Frame before write/read lowering" ]

def writeTyped (resultVar base : String) (write : CodeDataWrite) : Except String (List YulStmt) := do
  if !layoutSourcesSupported write.payload then
    throw "CodeData write payload has unsupported frame source"
  let (prelude, payloadArgs) := materializePayloadToMemory base write.payload
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
  if !layoutSourcesSupported read.payload then
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
    | .expr (.call "extcodecopy" _) => true
    | _ => false
  hasCreate2 && hasExtcodecopy

end Compiler.Modules.CodeData
