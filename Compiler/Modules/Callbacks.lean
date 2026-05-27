/-
  Compiler.Modules.Callbacks: Callback Pattern Modules

  Standard ECM for flash-loan-style callback invocations:
  - ABI-encode selector + static args + forwarded bytes parameter
  - Call target, revert-forward on failure

  Trust assumption: the callback target processes the encoded arguments correctly.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Callbacks

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

/-- Flash loan callback module.
    ABI-encodes `selector(staticArgs..., bytesParam)` and calls `target`.
    Reverts with returndata forwarding on failure.

    The module is parameterized by:
    - `selector`: the 4-byte function selector (must be < 2^32)
    - `numStaticArgs`: number of static (uint256/address) arguments
    - `bytesParam`: name of the bytes parameter (used to reference `{name}_length`
      and `{name}_data_offset` identifiers emitted by the calldata decoder)

    Arguments passed to compile: [target] ++ staticArgExprs
    (bytesParam length/offset are accessed via Yul identifiers, not as Expr arguments) -/
def callbackModule (selector : Nat) (numStaticArgs : Nat) (bytesParam : String)
    : ExternalCallModule where
  name := "callback"
  numArgs := 1 + numStaticArgs  -- target + static args
  writesState := true
  readsState := false
  axioms := ["callback_target_interface"]
  compile := fun ctx args => do
    if selector >= 2^32 then
      throw s!"callback: selector 0x{String.mk (Nat.toDigits 16 selector)} exceeds 4 bytes"
    if bytesParam.isEmpty then
      throw "callback: bytesParam must be non-empty"
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "callback expects at least 1 argument (target)"
    let staticArgExprs := args.drop 1
    -- Memory layout:
    --   [0..4]                          selector (shl(224, selector))
    --   [4..4+n*32]                     static args
    --   [4+n*32..+32]                   ABI offset to bytes data = (n+1)*32
    --   [4+(n+1)*32..+32]               bytes length
    --   [4+(n+2)*32..+len]              bytes data (calldatacopy/memcopy)
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let ptrName := "__cb_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := staticArgExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let bytesOffsetSlot := 4 + numStaticArgs * 32
    let bytesOffset := (numStaticArgs + 1) * 32
    let storeOffset := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [ptrExpr, YulExpr.lit bytesOffsetSlot],
      YulExpr.lit bytesOffset
    ])
    let bytesLenExpr := YulExpr.ident s!"{bytesParam}_length"
    let bytesLenSlot := 4 + (numStaticArgs + 1) * 32
    let storeBytesLen := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.call "add" [ptrExpr, YulExpr.lit bytesLenSlot],
      bytesLenExpr
    ])
    let bytesDataSlot := 4 + (numStaticArgs + 2) * 32
    let bytesDataOffset := YulExpr.ident s!"{bytesParam}_data_offset"
    let copyBytes := dynamicCopyData ctx
      (YulExpr.call "add" [ptrExpr, YulExpr.lit bytesDataSlot])
      bytesDataOffset
      bytesLenExpr
    let paddedBytesLen := YulExpr.call "and" [
      YulExpr.call "add" [bytesLenExpr, YulExpr.lit 31],
      YulExpr.call "not" [YulExpr.lit 31]
    ]
    let totalSize := YulExpr.call "add" [YulExpr.lit bytesDataSlot, paddedBytesLen]
    let paddedTotalSize := YulExpr.call "and" [
      YulExpr.call "add" [totalSize, YulExpr.lit 31],
      YulExpr.call "not" [YulExpr.lit 31]
    ]
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, paddedTotalSize]
    ])
    let callExpr := YulExpr.call "call" [
      YulExpr.call "gas" [],
      targetExpr,
      YulExpr.lit 0,
      ptrExpr, totalSize,
      YulExpr.lit 0, YulExpr.lit 0
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__cb_success"]) [
      YulStmt.let_ "__cb_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cb_rds"]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cb_rds"])
    ]
    pure [YulStmt.block (
      [loadPtr, storeSelector] ++ storeArgs ++ [storeOffset, storeBytesLen] ++ copyBytes ++
      [advancePtr, YulStmt.let_ "__cb_success" callExpr, revertBlock]
    )]

/-- Convenience: create a `Stmt.ecm` for a callback invocation.
    `staticArgs` are the non-bytes arguments; `bytesParam` is the name of the
    bytes parameter whose `_length` and `_data_offset` Yul identifiers will be
    referenced in the generated code. -/
def callback (target : Expr) (selector : Nat) (staticArgs : List Expr) (bytesParam : String)
    : Stmt :=
  .ecm (callbackModule selector staticArgs.length bytesParam) ([target] ++ staticArgs)

end Compiler.Modules.Callbacks
