/-
  Compiler.Modules.Calls: Generic External Call Modules

  Standard ECM for ABI-encoded external calls with a single uint256 return:
  - `withReturn`: call/staticcall with selector + args, revert-forward on failure,
    validate return data, bind result variable
  - `callWithValue`: generic ETH-aware call over an already prepared calldata
    slice, revert-forward on failure
  - `callWithValueBytes`: generic ETH-aware call over a bytes parameter,
    copying the payload to memory before the call
  - `bubblingValueCall`: arbitrary low-level call with caller-provided ETH value,
    caller-provided input/output memory slices, and exact revert-data bubbling
  - `selfDelegateMulticallBytes`: Solidity-style `multicall(bytes[])` over a
    calldata bytes-array parameter, using `delegatecall(address(), data)` for
    each element and bubbling exact revert data

  Trust assumption: the target contract's function matches the declared
  selector and ABI encoding. For `callWithValue`, the caller is responsible for
  preparing calldata at the supplied memory slice. `callWithValueBytes` copies a
  bytes parameter into memory before calling. For arbitrary low-level calls, the
  target contract behavior and calldata ABI are deliberately outside Verity core
  and are surfaced as an explicit ECM assumption. The multicall helper is
  intentionally scoped to self-delegatecall: storage context is the current
  contract's storage, and no caller-selected implementation address is exposed.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Calls

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

private def bubblingValueCallYul
    (targetExpr valueExpr inputOffsetExpr inputSizeExpr outputOffsetExpr outputSizeExpr : YulExpr) :
    List YulStmt :=
  let callExpr := YulExpr.call "call" [
    YulExpr.call "gas" [],
    targetExpr,
    valueExpr,
    inputOffsetExpr,
    inputSizeExpr,
    outputOffsetExpr,
    outputSizeExpr
  ]
  [YulStmt.block [
    YulStmt.let_ "__bvc_success" callExpr,
    YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__bvc_success"]) [
      YulStmt.let_ "__bvc_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__bvc_rds"
      ]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__bvc_rds"])
    ]
  ]]

def selfDelegateMulticallBytesBody
    (arrayParam ptrName indexName successName rdsName : String) : Except String (List YulStmt) := do
  if arrayParam.isEmpty then
    throw "selfDelegateMulticallBytes: arrayParam must be non-empty"
  let ptrExpr := YulExpr.ident ptrName
  let indexExpr := YulExpr.ident indexName
  let arrayDataOffset := YulExpr.ident s!"{arrayParam}_data_offset"
  let arrayLength := YulExpr.ident s!"{arrayParam}_length"
  let offsetTableBytes := YulExpr.call "mul" [arrayLength, YulExpr.lit 32]
  let elementOffsetSlot := YulExpr.call "add" [
    arrayDataOffset,
    YulExpr.call "mul" [indexExpr, YulExpr.lit 32]
  ]
  let paddedSizeExpr := YulExpr.call "and" [
    YulExpr.call "add" [YulExpr.ident "__mc_data_size", YulExpr.lit 31],
    YulExpr.call "not" [YulExpr.lit 31]
  ]
  pure [
    YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
    YulStmt.for_
      [YulStmt.let_ indexName (YulExpr.lit 0)]
      (YulExpr.call "lt" [indexExpr, arrayLength])
      [YulStmt.assign indexName (YulExpr.call "add" [indexExpr, YulExpr.lit 1])]
      [
        YulStmt.let_ "__mc_rel_offset" (YulExpr.call "calldataload" [elementOffsetSlot]),
        YulStmt.if_ (YulExpr.call "lt" [YulExpr.ident "__mc_rel_offset", offsetTableBytes]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.let_ "__mc_head_offset" (YulExpr.call "add" [arrayDataOffset, YulExpr.ident "__mc_rel_offset"]),
        YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__mc_head_offset",
          YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.let_ "__mc_data_size" (YulExpr.call "calldataload" [YulExpr.ident "__mc_head_offset"]),
        YulStmt.let_ "__mc_data_offset" (YulExpr.call "add" [YulExpr.ident "__mc_head_offset", YulExpr.lit 32]),
        YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__mc_data_size",
          YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.ident "__mc_data_offset"]
        ]) [
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.expr (YulExpr.call "calldatacopy" [
          ptrExpr,
          YulExpr.ident "__mc_data_offset",
          YulExpr.ident "__mc_data_size"
        ]),
        YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptrExpr, paddedSizeExpr]
        ]),
        YulStmt.let_ successName (YulExpr.call "delegatecall" [
          YulExpr.call "gas" [],
          YulExpr.call "address" [],
          ptrExpr,
          YulExpr.ident "__mc_data_size",
          YulExpr.lit 0,
          YulExpr.lit 0
        ]),
        YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident successName]) [
          YulStmt.let_ rdsName (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident rdsName
          ]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident rdsName])
        ]
      ]
  ]

theorem selfDelegateMulticallBytesBody_empty_param :
    selfDelegateMulticallBytesBody "" "__mc_ptr" "__mc_i" "__mc_success" "__mc_rds" =
      Except.error "selfDelegateMulticallBytes: arrayParam must be non-empty" := by
  rfl

/-- Generic external call with single uint256 return.
    ABI-encodes `selector(args...)`, calls/staticcalls target, reverts on failure,
    validates returndatasize >= 32, and binds the result.

    The module is parameterized by:
    - `resultVar`: name for the bound result variable
    - `selector`: the 4-byte function selector
    - `numArgs`: number of ABI-encoded arguments (not counting target)
    - `isStatic`: true for staticcall, false for call

    Arguments passed to compile: [target] ++ argExprs -/
def withReturnModule (resultVar : String) (selector : Nat) (numArgs : Nat) (isStatic : Bool)
    : ExternalCallModule where
  name := "externalCallWithReturn"
  numArgs := 1 + numArgs  -- target + args
  resultVars := [resultVar]
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  compile := fun _ctx args => do
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "externalCallWithReturn expects at least 1 argument (target)"
    let argExprs := args.drop 1
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let ptrName := "__ecwr_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let calldataSize := 4 + numArgs * 32
    let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit frameSize]
    ])
    let callExpr :=
      if isStatic then
        YulExpr.call "staticcall" [
          YulExpr.call "gas" [],
          targetExpr,
          ptrExpr, YulExpr.lit calldataSize,
          ptrExpr, YulExpr.lit 32
        ]
      else
        YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0,
          ptrExpr, YulExpr.lit calldataSize,
          ptrExpr, YulExpr.lit 32
        ]
    let letSuccess := YulStmt.let_ "__ecwr_success" callExpr
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecwr_success"]) [
      YulStmt.let_ "__ecwr_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecwr_rds"]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecwr_rds"])
    ]
    let sizeCheck := YulStmt.if_ (YulExpr.call "lt" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [ptrExpr])
    let callBlock := YulStmt.block ([loadPtr, storeSelector] ++ storeArgs ++ [advancePtr, letSuccess, revertBlock, sizeCheck, assignResult])
    pure [bindResult, callBlock]

/-- Convenience: create a `Stmt.ecm` for an external call with return.
    Replaces the former `Stmt.externalCallWithReturn` variant. -/
def withReturn (resultVar : String) (target : Expr) (selector : Nat)
    (args : List Expr) (isStatic : Bool := false) : Stmt :=
  .ecm (withReturnModule resultVar selector args.length isStatic) ([target] ++ args)

/-- Generic external call to a void (no-return) function.

    Identical ABI-encoding and revert-forward-on-failure behaviour to
    `withReturnModule`, but binds no result and performs no `returndatasize`
    check or return decode. This is the ECM behind statement-position typed
    interface calls whose method declares no return type (e.g. Aave V3
    `supply`/`borrow`, which are `void`): such callees leave returndata empty,
    so the strict 32-byte check in `withReturnModule` would revert *after* the
    callee already ran and committed state.

    The module is parameterized by:
    - `selector`: the 4-byte function selector
    - `numArgs`: number of ABI-encoded arguments (not counting target)

    Arguments passed to compile: [target] ++ argExprs -/
def noReturnModule (selector : Nat) (numArgs : Nat) (isStatic : Bool := false)
    : ExternalCallModule where
  name := "externalCallNoReturn"
  numArgs := 1 + numArgs  -- target + args
  resultVars := []
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  compile := fun _ctx args => do
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "externalCallNoReturn expects at least 1 argument (target)"
    let argExprs := args.drop 1
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let ptrName := "__ecnr_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let storeSelector := YulStmt.expr (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.expr (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let calldataSize := 4 + numArgs * 32
    let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit frameSize]
    ])
    -- no output slice: return data is intentionally ignored
    let opcode := if isStatic then "staticcall" else "call"
    let callArgs :=
      if isStatic then
        [ YulExpr.call "gas" []
        , targetExpr
        , ptrExpr, YulExpr.lit calldataSize
        , YulExpr.lit 0, YulExpr.lit 0 ]
      else
        [ YulExpr.call "gas" []
        , targetExpr
        , YulExpr.lit 0
        , ptrExpr, YulExpr.lit calldataSize
        , YulExpr.lit 0, YulExpr.lit 0 ]
    let callExpr :=
      YulExpr.call opcode callArgs
    let letSuccess := YulStmt.let_ "__ecnr_success" callExpr
    -- bubble failure returndata exactly, like withReturnModule; but on success
    -- do NOT check returndatasize or decode a return value
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecnr_success"]) [
      YulStmt.let_ "__ecnr_rds" (YulExpr.call "returndatasize" []),
      YulStmt.expr (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecnr_rds"]),
      YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecnr_rds"])
    ]
    pure [YulStmt.block ([loadPtr, storeSelector] ++ storeArgs ++ [advancePtr, letSuccess, revertBlock])]

/-- Convenience: create a `Stmt.ecm` for a void external call (no return). -/
def noReturn (target : Expr) (selector : Nat) (args : List Expr) (isStatic : Bool := false) : Stmt :=
  .ecm (noReturnModule selector args.length isStatic) ([target] ++ args)

/-- Generic Solidity-style low-level value call with revert-data bubbling.

    This models the common wrapper:

    ```
    let success := call(gas(), target, value, inputOffset, inputSize, outputOffset, outputSize)
    if iszero(success) {
      returndatacopy(0, 0, returndatasize())
      revert(0, returndatasize())
    }
    ```

    Arguments passed to compile:
    `[target, value, inputOffset, inputSize, outputOffset, outputSize]`.

    The module intentionally does not interpret the calldata or returndata
    payload. Protocol-specific meaning belongs in packages that use this generic
    Verity-core mechanism and document their own assumptions. -/
def bubblingValueCallModule : ExternalCallModule where
  name := "bubblingValueCall"
  numArgs := 6
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_low_level_value_call_interface"]
  compile := fun _ctx args => do
    let (targetExpr, valueExpr, inputOffsetExpr, inputSizeExpr, outputOffsetExpr, outputSizeExpr) ←
      match args with
      | [target, value, inputOffset, inputSize, outputOffset, outputSize] =>
          pure (target, value, inputOffset, inputSize, outputOffset, outputSize)
      | _ =>
          throw "bubblingValueCall expects 6 arguments (target, value, inputOffset, inputSize, outputOffset, outputSize)"
    pure <| bubblingValueCallYul
      targetExpr valueExpr inputOffsetExpr inputSizeExpr outputOffsetExpr outputSizeExpr

/-- Four-argument no-output variant of `bubblingValueCallModule`.

    This is useful for `verity_contract` `ecmDo` call sites and for adapter or
    router calls where successful returndata is intentionally ignored. Failure
    returndata is still bubbled exactly. -/
def bubblingValueCallNoOutputModule : ExternalCallModule where
  name := "bubblingValueCallNoOutput"
  numArgs := 4
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_low_level_value_call_interface"]
  compile := fun _ctx args => do
    let (targetExpr, valueExpr, inputOffsetExpr, inputSizeExpr) ←
      match args with
      | [target, value, inputOffset, inputSize] =>
          pure (target, value, inputOffset, inputSize)
      | _ =>
          throw "bubblingValueCallNoOutput expects 4 arguments (target, value, inputOffset, inputSize)"
    pure <| bubblingValueCallYul
      targetExpr valueExpr inputOffsetExpr inputSizeExpr (YulExpr.lit 0) (YulExpr.lit 0)

/-- Convenience constructor for `bubblingValueCallModule`. -/
def bubblingValueCall
    (target value inputOffset inputSize outputOffset outputSize : Expr) : Stmt :=
  .ecm bubblingValueCallModule [target, value, inputOffset, inputSize, outputOffset, outputSize]

/-- Convenience constructor for the common adapter/router shape that ignores
    successful returndata while still bubbling failure returndata exactly. -/
def bubblingValueCallNoOutput
    (target value inputOffset inputSize : Expr) : Stmt :=
  .ecm bubblingValueCallNoOutputModule [target, value, inputOffset, inputSize]

/-- ETH-aware generic external call over an already prepared calldata slice.

    Arguments passed to compile: [target, value, inOffset, inSize].
    The module emits `call(gas(), target, value, inOffset, inSize, 0, 0)`,
    bubbles revert returndata on failure, and ignores successful returndata.

    This is intentionally lower-level than `withReturn`: it is the standard ECM
    for adapter/router patterns that need arbitrary calldata plus `call{value:v}`.
    The caller is responsible for constructing calldata and decoding or ignoring
    any successful returndata. -/
def callWithValueModule : ExternalCallModule where
  name := "callWithValue"
  numArgs := 4
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_call_with_value_interface"]
  compile := fun _ctx args => do
    match args with
    | [targetExpr, valueExpr, inOffsetExpr, inSizeExpr] =>
        let callExpr := YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          valueExpr,
          inOffsetExpr, inSizeExpr,
          YulExpr.lit 0, YulExpr.lit 0
        ]
        let letSuccess := YulStmt.let_ "__cwv_success" callExpr
        let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__cwv_success"]) [
          YulStmt.let_ "__cwv_rds" (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
        ]
        pure [YulStmt.block [letSuccess, revertBlock]]
    | _ =>
        throw "callWithValue expects 4 arguments (target, value, inOffset, inSize)"

/-- Convenience: create a `Stmt.ecm` for an ETH-aware generic call. -/
def callWithValue (target value inOffset inSize : Expr) : Stmt :=
  .ecm callWithValueModule [target, value, inOffset, inSize]

/-- ETH-aware generic external call over a bytes parameter.

    Arguments passed to compile: [target, value].
    The module reads `{bytesParam}_data_offset` and `{bytesParam}_length` from
    the function decoder, copies that bytes payload to the free-memory region,
    emits `call(gas(), target, value, ptr, {bytesParam}_length, 0, 0)`, bubbles
    revert returndata on failure, and ignores successful returndata.

    This is the higher-level `(target, value, data)` surface for adapter/router
    patterns. The raw-slice `callWithValueModule` remains available when callers
    have already prepared calldata in memory. -/
def callWithValueBytesModule (bytesParam : String) : ExternalCallModule where
  name := "callWithValueBytes"
  numArgs := 2
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["generic_call_with_value_interface"]
  compile := fun ctx args => do
    if bytesParam.isEmpty then
      throw "callWithValueBytes: bytesParam must be non-empty"
    match args with
    | [targetExpr, valueExpr] =>
        let dataOffsetExpr := YulExpr.ident s!"{bytesParam}_data_offset"
        let dataSizeExpr := YulExpr.ident s!"{bytesParam}_length"
        let ptrName := "__cwv_bytes_ptr"
        let ptrExpr := YulExpr.ident ptrName
        let paddedName := "__cwv_bytes_padded"
        let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
        let copyData := dynamicCopyData ctx ptrExpr dataOffsetExpr dataSizeExpr
        let computePadded := YulStmt.let_ paddedName (YulExpr.call "and" [
          YulExpr.call "add" [dataSizeExpr, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ])
        let advancePtr := YulStmt.expr (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptrExpr, YulExpr.ident paddedName]
        ])
        let callExpr := YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          valueExpr,
          ptrExpr, dataSizeExpr,
          YulExpr.lit 0, YulExpr.lit 0
        ]
        let letSuccess := YulStmt.let_ "__cwv_success" callExpr
        let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__cwv_success"]) [
          YulStmt.let_ "__cwv_rds" (YulExpr.call "returndatasize" []),
          YulStmt.expr (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.expr (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
        ]
        pure [YulStmt.block ([loadPtr] ++ copyData ++ [computePadded, advancePtr, letSuccess, revertBlock])]
    | _ =>
        throw "callWithValueBytes expects 2 arguments (target, value)"

/-- Convenience: create a `Stmt.ecm` for an ETH-aware generic call over a bytes
    parameter named `bytesParam`. -/
def callWithValueBytes (target value : Expr) (bytesParam : String) : Stmt :=
  .ecm (callWithValueBytesModule bytesParam) [target, value]

/-- Source-level `multicall(bytes[])` helper for self-delegatecall routers.

    The named parameter must be a `bytes[]` ABI parameter. The generated Yul
    walks the ABI offset table, copies each element payload into memory, then
    executes `delegatecall(gas(), address(), ptr, size, 0, 0)`. On failure it
    forwards returndata exactly with `returndatacopy(0, 0, returndatasize())`
    followed by `revert(0, returndatasize())`.

    Unlike the general `Expr.delegatecall` surface, this module has no dynamic
    implementation address and is intended for same-contract multicall only. -/
def selfDelegateMulticallBytesModule (arrayParam : String) : ExternalCallModule where
  name := "selfDelegateMulticallBytes"
  numArgs := 0
  resultVars := []
  writesState := true
  readsState := true
  axioms := ["self_delegate_multicall_bytes_revert_bubbling"]
  compile := fun _ctx args => do
    match args with
    | [] =>
        selfDelegateMulticallBytesBody arrayParam "__mc_ptr" "__mc_i" "__mc_success" "__mc_rds"
    | _ =>
        throw "selfDelegateMulticallBytes expects 0 arguments"

/-- Convenience constructor for self-delegatecall `multicall(bytes[])`. -/
def selfDelegateMulticallBytes (arrayParam : String) : Stmt :=
  .ecm (selfDelegateMulticallBytesModule arrayParam) []

end Compiler.Modules.Calls
