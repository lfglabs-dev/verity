/-
  Compiler.Modules.Calls: Generic External Call Modules

  Standard ECM for ABI-encoded external calls with a single uint256 return:
  - `withReturn`: call/staticcall with selector + args, revert-forward on failure,
    validate return data, bind result variable
  - `withReturnsModule`: same, binding several static return words (typed
    interface tuple calls on non-view methods)
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
      YulStmt.exprStmt (YulExpr.call "returndatacopy" [
        YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__bvc_rds"
      ]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__bvc_rds"])
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
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__mc_rel_offset",
          YulExpr.call "sub" [
            YulExpr.call "not" [YulExpr.lit 0],
            arrayDataOffset
          ]
        ]) [
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.let_ "__mc_head_offset" (YulExpr.call "add" [arrayDataOffset, YulExpr.ident "__mc_rel_offset"]),
        YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__mc_head_offset",
          YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.lit 32]
        ]) [
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.let_ "__mc_data_size" (YulExpr.call "calldataload" [YulExpr.ident "__mc_head_offset"]),
        YulStmt.let_ "__mc_data_offset" (YulExpr.call "add" [YulExpr.ident "__mc_head_offset", YulExpr.lit 32]),
        YulStmt.if_ (YulExpr.call "gt" [
          YulExpr.ident "__mc_data_size",
          YulExpr.call "sub" [YulExpr.call "calldatasize" [], YulExpr.ident "__mc_data_offset"]
        ]) [
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
        ],
        YulStmt.exprStmt (YulExpr.call "calldatacopy" [
          ptrExpr,
          YulExpr.ident "__mc_data_offset",
          YulExpr.ident "__mc_data_size"
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
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
          YulStmt.exprStmt (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident rdsName
          ]),
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident rdsName])
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
    let storeSelector := YulStmt.exprStmt (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let calldataSize := 4 + numArgs * 32
    let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let advancePtr := YulStmt.exprStmt (YulExpr.call "mstore" [
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
      YulStmt.exprStmt (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecwr_rds"]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecwr_rds"])
    ]
    let sizeCheck := YulStmt.if_ (YulExpr.call "lt" [YulExpr.call "returndatasize" [], YulExpr.lit 32]) [
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResult := YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResult := YulStmt.assign resultVar (YulExpr.call "mload" [ptrExpr])
    let callBlock := YulStmt.block ([loadPtr, storeSelector] ++ storeArgs ++ [advancePtr, letSuccess, revertBlock, sizeCheck, assignResult])
    pure [bindResult, callBlock]

/-- Generic external call with several static ABI-word returns (G14, mutable
    typed-interface tuple calls such as `let (a, b) ← s.prepare x`).
    ABI-encodes `selector(args...)`, calls/staticcalls target, forwards revert
    returndata on failure, requires `returndatasize >= 32 * resultVars.length`,
    and binds word `i` of the return frame to `resultVars[i]`.

    Arguments passed to compile: [target] ++ argExprs -/
def withReturnsModule (resultVars : List String) (selector : Nat) (numArgs : Nat)
    (isStatic : Bool) : ExternalCallModule where
  name := "externalCallWithReturns"
  numArgs := 1 + numArgs  -- target + args
  resultVars := resultVars
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  compile := fun _ctx args => do
    let targetExpr ← match args.head? with
      | some t => pure t
      | none => throw "externalCallWithReturns expects at least 1 argument (target)"
    if resultVars.isEmpty then
      throw "externalCallWithReturns expects at least one result variable"
    let argExprs := args.drop 1
    let selectorExpr := YulExpr.call "shl" [YulExpr.lit 224, YulExpr.hex selector]
    let ptrName := "__ecwrs_ptr"
    let ptrExpr := YulExpr.ident ptrName
    let storeSelector := YulStmt.exprStmt (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let calldataSize := 4 + numArgs * 32
    let returndataSize := resultVars.length * 32
    let frameSize := ((Nat.max calldataSize returndataSize + 31) / 32) * 32
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let advancePtr := YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.lit freeMemoryPointer,
      YulExpr.call "add" [ptrExpr, YulExpr.lit frameSize]
    ])
    let callExpr :=
      if isStatic then
        YulExpr.call "staticcall" [
          YulExpr.call "gas" [],
          targetExpr,
          ptrExpr, YulExpr.lit calldataSize,
          ptrExpr, YulExpr.lit returndataSize
        ]
      else
        YulExpr.call "call" [
          YulExpr.call "gas" [],
          targetExpr,
          YulExpr.lit 0,
          ptrExpr, YulExpr.lit calldataSize,
          ptrExpr, YulExpr.lit returndataSize
        ]
    let letSuccess := YulStmt.let_ "__ecwrs_success" callExpr
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__ecwrs_success"]) [
      YulStmt.let_ "__ecwrs_rds" (YulExpr.call "returndatasize" []),
      YulStmt.exprStmt (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecwrs_rds"]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecwrs_rds"])
    ]
    let sizeCheck := YulStmt.if_ (YulExpr.call "lt" [YulExpr.call "returndatasize" [], YulExpr.lit returndataSize]) [
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    let bindResults := resultVars.map fun resultVar => YulStmt.let_ resultVar (YulExpr.lit 0)
    let assignResults := resultVars.zipIdx.map fun (resultVar, idx) =>
      YulStmt.assign resultVar (YulExpr.call "mload" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (idx * 32)]])
    let callBlock := YulStmt.block ([loadPtr, storeSelector] ++ storeArgs ++
      [advancePtr, letSuccess, revertBlock, sizeCheck] ++ assignResults)
    pure (bindResults ++ [callBlock])

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
    let storeSelector := YulStmt.exprStmt (YulExpr.call "mstore" [ptrExpr, selectorExpr])
    let storeArgs := argExprs.zipIdx.map fun (argExpr, i) =>
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.call "add" [ptrExpr, YulExpr.lit (4 + i * 32)],
        argExpr
      ])
    let calldataSize := 4 + numArgs * 32
    let frameSize := ((Nat.max calldataSize 32 + 31) / 32) * 32
    let loadPtr := YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
    let advancePtr := YulStmt.exprStmt (YulExpr.call "mstore" [
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
      YulStmt.exprStmt (YulExpr.call "returndatacopy" [YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__ecnr_rds"]),
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__ecnr_rds"])
    ]
    pure [YulStmt.block ([loadPtr, storeSelector] ++ storeArgs ++ [advancePtr, letSuccess, revertBlock])]

/-- Convenience: create a `Stmt.ecm` for a void external call (no return). -/
def noReturn (target : Expr) (selector : Nat) (args : List Expr) (isStatic : Bool := false) : Stmt :=
  .ecm (noReturnModule selector args.length isStatic) ([target] ++ args)

/-! ### ABI-frame typed-interface calls

`abiCallModule` encodes a call with Solidity's head/tail ABI layout, so that a
typed-interface method may take `bytes` arguments and return `(bool, bytes)`.
A `bytes` argument is either a `bytes` parameter of the calling function
(`{name}_data_offset` / `{name}_length`, from calldata or memory) or a payload
built in place, `abi.encodeWithSelector(selector, items...)`, whose items are
words or `bytes` parameters. The generated Yul keeps few locals alive (one
frame pointer and one running tail offset per nesting level), so that calls
with many arguments stay within the EVM stack. -/

/-- An item of a payload built in place: a word, or a `bytes` parameter. -/
inductive AbiCallItemShape where
  | word
  | bytesParam (name : String)
  deriving Repr, BEq, DecidableEq

/-- An argument of an ABI-frame call: a word (the next `Expr` argument), a
`bytes` parameter, or a payload `abi.encodeWithSelector(selector, items...)`. -/
inductive AbiCallArgShape where
  | word
  | bytesParam (name : String)
  | encodedCall (selector : Nat) (items : List AbiCallItemShape)
  deriving Repr, BEq, DecidableEq

/-- What an ABI-frame call decodes: `words vars` binds the first
`vars.length` return words (no check when empty, as `noReturnModule`);
`boolBytes ok b` decodes a Solidity `(bool, bytes)` return into `ok` and a
memory copy of the bytes, bound as the word array `{b}_words`:
`{b}_words_data_offset` points at the length word, followed by the data, and
`{b}_words_length = length / 32 + 2` words, the ones past the data zero. -/
inductive AbiCallReturnShape where
  | words (vars : List String)
  | boolBytes (okVar bytesName : String)
  deriving Repr, BEq, DecidableEq

def AbiCallItemShape.wordCount : AbiCallItemShape → Nat
  | .word => 1
  | .bytesParam _ => 0

def AbiCallArgShape.wordCount : AbiCallArgShape → Nat
  | .word => 1
  | .bytesParam _ => 0
  | .encodedCall _ items => (items.map AbiCallItemShape.wordCount).sum

/-- The word array holding the bytes of a `boolBytes` return named `bytesName`. -/
def abiReturnBytesArrayName (bytesName : String) : String :=
  s!"{bytesName}_words"

def AbiCallReturnShape.vars : AbiCallReturnShape → List String
  | .words vars => vars
  | .boolBytes okVar bytesName =>
      [okVar, s!"{abiReturnBytesArrayName bytesName}_data_offset",
        s!"{abiReturnBytesArrayName bytesName}_length"]

private def abiLit (n : Nat) : YulExpr := YulExpr.lit n
private def abiId (name : String) : YulExpr := YulExpr.ident name
private def abiCall (fn : String) (args : List YulExpr) : YulExpr := YulExpr.call fn args
private def abiStore (offset value : YulExpr) : YulStmt :=
  YulStmt.exprStmt (abiCall "mstore" [offset, value])
private def abiRevertEmptyIf (cond : YulExpr) : YulStmt :=
  YulStmt.if_ cond [YulStmt.exprStmt (abiCall "revert" [abiLit 0, abiLit 0])]
/-- `(x + 31) & ~31`. -/
private def abiPad32 (x : YulExpr) : YulExpr :=
  abiCall "and" [abiCall "add" [x, abiLit 31], abiCall "not" [abiLit 31]]

/-- Write the tail of a `bytes` value at the running tail offset `tailVar` of
the argument block starting at `base`: its length word, its data, zero
padding (a whole zero word after the data; a later tail overwrites it); then
advance `tailVar` past it. -/
private def abiBytesTail (ctx : CompilationContext) (base : YulExpr) (tailVar : String)
    (dataOffset length : YulExpr) : List YulStmt :=
  let dst := abiCall "add" [base, abiId tailVar]
  let data := abiCall "add" [dst, abiLit 32]
  [abiStore dst length] ++
    dynamicCopyData ctx data dataOffset length ++ [
    abiStore (abiCall "add" [data, length]) (abiLit 0),
    YulStmt.assign tailVar (abiCall "add" [abiId tailVar,
      abiCall "add" [abiLit 32, abiPad32 length]])]

/-- Encode the heads and tails of `items` in the argument block at `base`, with
running tail offset `tailVar` (declared here); `words` are the item words. -/
private def abiEncodeItemsAt (ctx : CompilationContext) (base : YulExpr) (tailVar : String)
    (items : List AbiCallItemShape) (words : List YulExpr) : Except String (List YulStmt) := do
  let mut stmts : List YulStmt := [YulStmt.let_ tailVar (abiLit (32 * items.length))]
  let mut rest := words
  for (item, j) in items.zipIdx do
    let head := abiCall "add" [base, abiLit (32 * j)]
    match item with
    | .word =>
        match rest with
        | w :: tail =>
            stmts := stmts ++ [abiStore head w]
            rest := tail
        | [] => throw "externalCallAbi: missing item word"
    | .bytesParam name =>
        stmts := stmts ++ [abiStore head (abiId tailVar)] ++
          abiBytesTail ctx base tailVar (abiId s!"{name}_data_offset") (abiId s!"{name}_length")
  pure stmts

/-- Yul of `abiCallModule` over its compiled arguments `[target] ++ words`. -/
def abiCallBody (ctx : CompilationContext) (selector : Nat) (shapes : List AbiCallArgShape)
    (ret : AbiCallReturnShape) (isStatic : Bool) (args : List YulExpr) :
    Except String (List YulStmt) := do
  if selector ≥ 2 ^ 32 then
    throw "externalCallAbi: selector exceeds 4 bytes"
  let (targetExpr, wordExprs) ← match args with
    | t :: ws => pure (t, ws)
    | [] => throw "externalCallAbi expects at least 1 argument (target)"
  unless wordExprs.length == (shapes.map AbiCallArgShape.wordCount).sum do
    throw "externalCallAbi: argument words differ from the argument shapes"
  let ptr := abiId "__abi_ptr"
  let base := abiCall "add" [ptr, abiLit 4]
  let tailVar := "__abi_tail"
  let mut encode : List YulStmt := [
    YulStmt.let_ "__abi_ptr" (abiCall "mload" [abiLit freeMemoryPointer]),
    abiStore ptr (abiCall "shl" [abiLit 224, YulExpr.hex selector]),
    YulStmt.let_ tailVar (abiLit (32 * shapes.length))]
  let mut rest := wordExprs
  for (shape, i) in shapes.zipIdx do
    let head := abiCall "add" [base, abiLit (32 * i)]
    match shape with
    | .word =>
        match rest with
        | w :: tail =>
            encode := encode ++ [abiStore head w]
            rest := tail
        | [] => throw "externalCallAbi: missing argument word"
    | .bytesParam name =>
        encode := encode ++ [abiStore head (abiId tailVar)] ++
          abiBytesTail ctx base tailVar (abiId s!"{name}_data_offset") (abiId s!"{name}_length")
    | .encodedCall sel items =>
        if sel ≥ 2 ^ 32 then
          throw "externalCallAbi: encoded-call selector exceeds 4 bytes"
        -- The payload is a `bytes` tail: a length word, then `selector ++ items`.
        let count := (AbiCallArgShape.encodedCall sel items).wordCount
        let itemWords := rest.take count
        rest := rest.drop count
        let dst := abiCall "add" [base, abiId tailVar]
        let inner := abiCall "add" [dst, abiLit 32]
        let innerTail := "__abi_itail"
        let itemStmts ← abiEncodeItemsAt ctx (abiCall "add" [inner, abiLit 4]) innerTail
          items itemWords
        let payloadLength := abiCall "add" [abiLit 4, abiId innerTail]
        encode := encode ++ [abiStore head (abiId tailVar),
          YulStmt.block ([abiStore inner (abiCall "shl" [abiLit 224, YulExpr.hex sel])] ++
            itemStmts ++ [
            abiStore dst payloadLength,
            abiStore (abiCall "add" [inner, payloadLength]) (abiLit 0),
            YulStmt.assign tailVar (abiCall "add" [abiId tailVar,
              abiCall "add" [abiLit 32, abiPad32 payloadLength]])])]
  let size := abiCall "add" [abiLit 4, abiId tailVar]
  -- One spare word: the zero padding store of the last tail may reach it.
  encode := encode ++ [abiStore (abiLit freeMemoryPointer)
    (abiCall "add" [ptr, abiPad32 (abiCall "add" [size, abiLit 32])])]
  let callExpr :=
    if isStatic then
      abiCall "staticcall" [abiCall "gas" [], targetExpr, ptr, size, abiLit 0, abiLit 0]
    else
      abiCall "call" [abiCall "gas" [], targetExpr, abiLit 0, ptr, size, abiLit 0, abiLit 0]
  let bubble := YulStmt.if_ (abiCall "iszero" [callExpr]) [
    YulStmt.exprStmt (abiCall "returndatacopy" [abiLit 0, abiLit 0, abiCall "returndatasize" []]),
    YulStmt.exprStmt (abiCall "revert" [abiLit 0, abiCall "returndatasize" []])]
  let out := abiId "__abi_out"
  let rds := abiCall "returndatasize" []
  let decode : List YulStmt := match ret with
    | .words [] => []
    | .words vars => [
        abiRevertEmptyIf (abiCall "lt" [rds, abiLit (32 * vars.length)]),
        YulStmt.let_ "__abi_out" (abiCall "mload" [abiLit freeMemoryPointer]),
        YulStmt.exprStmt (abiCall "returndatacopy" [out, abiLit 0, abiLit (32 * vars.length)])] ++
        vars.zipIdx.map fun (v, idx) =>
          YulStmt.assign v (abiCall "mload" [abiCall "add" [out, abiLit (32 * idx)]])
    | .boolBytes okVar bytesName =>
        let arrayName := abiReturnBytesArrayName bytesName
        let lengthWordVar := s!"{arrayName}_data_offset"
        let lengthWord := abiId lengthWordVar
        let length := abiCall "mload" [lengthWord]
        let maxU64 := abiLit (2 ^ 64 - 1)
        let offset := abiId "__abi_offset"
        -- solc's `(bool, bytes)` decoder checks; any failure reverts with empty data.
        [ abiRevertEmptyIf (abiCall "lt" [rds, abiLit 64]),
          YulStmt.let_ "__abi_out" (abiCall "mload" [abiLit freeMemoryPointer]),
          YulStmt.exprStmt (abiCall "returndatacopy" [out, abiLit 0, rds]),
          -- The copy, plus one spare word for the zero padding store below.
          abiStore (abiLit freeMemoryPointer)
            (abiCall "add" [out, abiPad32 (abiCall "add" [rds, abiLit 32])]),
          YulStmt.assign okVar (abiCall "mload" [out]),
          abiRevertEmptyIf (abiCall "gt" [abiId okVar, abiLit 1]),
          YulStmt.let_ "__abi_offset" (abiCall "mload" [abiCall "add" [out, abiLit 32]]),
          abiRevertEmptyIf (abiCall "gt" [offset, maxU64]),
          abiRevertEmptyIf (abiCall "gt" [abiCall "add" [offset, abiLit 32], rds]),
          YulStmt.assign lengthWordVar (abiCall "add" [out, offset]),
          abiRevertEmptyIf (abiCall "gt" [length, maxU64]),
          abiRevertEmptyIf (abiCall "gt"
            [abiCall "add" [abiCall "add" [offset, abiLit 32], length], rds]),
          -- Bytes past the end read as zero (`bytesWord`).
          abiStore (abiCall "add" [abiCall "add" [lengthWord, abiLit 32], length]) (abiLit 0),
          YulStmt.assign s!"{arrayName}_length"
            (abiCall "add" [abiCall "shr" [abiLit 5, length], abiLit 2])]
  -- Results are declared after the call, so they take no stack slot while encoding.
  let bindResults := ret.vars.map fun v => YulStmt.let_ v (abiLit 0)
  pure ([YulStmt.block (encode ++ [bubble])] ++ bindResults ++
    (if decode.isEmpty then [] else [YulStmt.block decode]))

/-- ABI-frame typed-interface call: `selector(args...)` with Solidity's
head/tail layout (`bytes` arguments allowed, see `AbiCallArgShape`), `call`
or `staticcall` of the target, exact revert-data bubbling on failure, then
the return decoding of `ret` (see `AbiCallReturnShape`; malformed returndata
reverts with empty data). Arguments: `[target] ++ words`, the words of the
shapes in order. -/
def abiCallModule (selector : Nat) (shapes : List AbiCallArgShape)
    (ret : AbiCallReturnShape) (isStatic : Bool) : ExternalCallModule where
  name := "externalCallAbi"
  numArgs := 1 + (shapes.map AbiCallArgShape.wordCount).sum
  resultVars := ret.vars
  writesState := !isStatic
  readsState := true
  axioms := ["external_call_abi_interface"]
  summarySelector := some selector
  compile := fun ctx args => abiCallBody ctx selector shapes ret isStatic args

/-- `revert(data, length)` of a memory byte range: `revertBytes ret` for the
`bytes` return of an ABI-frame call. -/
def revertMemoryBytesModule : ExternalCallModule where
  name := "revertMemoryBytes"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx args =>
    match args with
    | [data, length] => pure [YulStmt.exprStmt (YulExpr.call "revert" [data, length])]
    | _ => throw "revertMemoryBytes expects 2 arguments (data, length)"

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
  targetArg := some 0
  valueArg := some 1
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
  targetArg := some 0
  valueArg := some 1
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
  targetArg := some 0
  valueArg := some 1
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
          YulStmt.exprStmt (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
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
  targetArg := some 0
  valueArg := some 1
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
        let advancePtr := YulStmt.exprStmt (YulExpr.call "mstore" [
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
          YulStmt.exprStmt (YulExpr.call "returndatacopy" [
            YulExpr.lit 0, YulExpr.lit 0, YulExpr.ident "__cwv_rds"
          ]),
          YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.ident "__cwv_rds"])
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
