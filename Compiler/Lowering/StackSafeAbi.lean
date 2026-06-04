import Compiler.ABI.Frame

namespace Compiler.Lowering.StackSafeAbi

open Compiler.ABI.Frame
open Compiler.Yul

structure LoweredFrame where
  prologue : List YulStmt
  args : List YulExpr
  layout : FrameLayout
  deriving Repr

def lowerFrameSpilled (base : String) (fields : List FrameField) : Except String LoweredFrame := do
  let l := layout fields
  if !layoutSourcesSupported l then
    throw s!"ABI frame '{base}' uses an unsupported source"
  let prologue :=
    match l.mode with
    | .pointer => spillPayloadToMemory base l
    | .inlineWords => []
  pure { prologue, args := loweredArgs base l, layout := l }

def lowerEvent (eventName : String) (fields : List FrameField) : Except String (List YulStmt) := do
  let lowered ← lowerFrameSpilled eventName fields
  match lowered.layout.mode with
  | .pointer =>
      pure (lowered.prologue ++
        [YulStmt.expr (YulExpr.call "log1" (lowered.args ++ [YulExpr.call "keccak256" [YulExpr.str eventName, YulExpr.lit 0]]))])
  | .inlineWords =>
      pure (lowered.prologue ++
        [YulStmt.expr (YulExpr.call "log1" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.call "keccak256" [YulExpr.str eventName, YulExpr.lit 0]])])

def lowerExternalCall (callName : String) (target value : YulExpr) (fields : List FrameField) : Except String (List YulStmt) := do
  let lowered ← lowerFrameSpilled callName fields
  let callArgs :=
    match lowered.layout.mode with
    | .pointer => [YulExpr.call "gas" [], target, value] ++ lowered.args ++ [YulExpr.lit 0, YulExpr.lit 0]
    | .inlineWords => [YulExpr.call "gas" [], target, value, YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0, YulExpr.lit 0]
  pure (lowered.prologue ++ [YulStmt.let_ ("__" ++ callName ++ "_ok") (YulExpr.call "call" callArgs)])

def lowerDynamicReturn (returnName : String) (fields : List FrameField) : Except String (List YulStmt) := do
  let lowered ← lowerFrameSpilled returnName fields
  match lowered.layout.mode with
  | .pointer => pure (lowered.prologue ++ [YulStmt.expr (YulExpr.call "return" lowered.args)])
  | .inlineWords => pure (lowered.prologue ++ [YulStmt.expr (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])])

def usesPointerAbi (stmts : List YulStmt) : Bool :=
  stmts.any fun stmt =>
    match stmt with
    | .expr (.call "return" [_ptr, _size]) => true
    | .expr (.call "log1" [_ptr, _size, _topic]) => true
    | .let_ _ (.call "call" [_gas, _target, _value, _ptr, _size, _out, _outSize]) => true
    | _ => false

end Compiler.Lowering.StackSafeAbi
