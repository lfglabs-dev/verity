import Compiler.ABI.Frame

namespace Compiler.Lowering.StackSafeAbi

open Compiler.ABI.Frame
open Compiler.Yul

structure LoweredFrame where
  prologue : List YulStmt
  args : List YulExpr
  layout : FrameLayout
  deriving Repr

def eventNameTopicWord (eventName : String) : Nat :=
  UInt64.toNat (hash eventName)

def lowerFrameSpilled (base : String) (fields : List FrameField) : Except String LoweredFrame := do
  let l := layout fields
  if !layoutSourcesSupported l then
    throw s!"ABI frame '{base}' uses an unsupported source"
  let prologue :=
    match l.mode with
    | .pointer => spillPayloadToMemory base l
    | .inlineWords => []
  pure { prologue, args := loweredArgs base l, layout := l }

def lowerFrameAsMemoryPayload (base : String) (fields : List FrameField) : Except String (List YulStmt × List YulExpr × FrameLayout) := do
  let lowered ← lowerFrameSpilled base fields
  let (prologue, args) := materializePayloadToMemory base lowered.layout
  pure (prologue, args, lowered.layout)

def lowerEventWithTopic (base : String) (topic0 : YulExpr) (fields : List FrameField) : Except String (List YulStmt) := do
  let (prologue, payloadArgs, _) ← lowerFrameAsMemoryPayload base fields
  pure (prologue ++
    [YulStmt.expr (YulExpr.call "log1" (payloadArgs ++ [topic0]))])

def lowerEvent (eventName : String) (fields : List FrameField) : Except String (List YulStmt) := do
  lowerEventWithTopic eventName (YulExpr.lit (eventNameTopicWord eventName)) fields

def lowerExternalCall (callName : String) (target value : YulExpr) (fields : List FrameField) : Except String (List YulStmt) := do
  let (prologue, payloadArgs, _) ← lowerFrameAsMemoryPayload callName fields
  let callArgs := [YulExpr.call "gas" [], target, value] ++ payloadArgs ++ [YulExpr.lit 0, YulExpr.lit 0]
  pure (prologue ++ [YulStmt.let_ ("__" ++ callName ++ "_ok") (YulExpr.call "call" callArgs)])

def lowerDynamicReturn (returnName : String) (fields : List FrameField) : Except String (List YulStmt) := do
  let (prologue, payloadArgs, _) ← lowerFrameAsMemoryPayload returnName fields
  pure (prologue ++ [YulStmt.expr (YulExpr.call "return" payloadArgs)])

def usesPointerAbi (stmts : List YulStmt) : Bool :=
  stmts.any fun stmt =>
    match stmt with
    | .expr (.call "return" [_ptr, _size]) => true
    | .expr (.call "log1" [_ptr, _size, _topic]) => true
    | .let_ _ (.call "call" [_gas, _target, _value, _ptr, _size, _out, _outSize]) => true
    | _ => false

end Compiler.Lowering.StackSafeAbi
