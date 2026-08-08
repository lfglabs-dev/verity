import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

-- P0 #1003 coverage for linked calls and explicit low-level body syntax.
-- `callExternal` is declaration-driven; target/value fields belong to `evmCall`.
verity_contract ExternalCallInBodySmoke where
  storage
  linked_externals
    external getDepositableEther() -> (Uint256)
    external deposit(Uint256, Bytes)

  function reentrancy_trusted linkedRead () : Uint256 := do
    let depositable ← callExternal getDepositableEther()
    return depositable

  function reentrancy_trusted linkedWrite (amount : Uint256, pubkey : Bytes) : Unit := do
    callExternal deposit(amount, pubkey)

  function reentrancy_trusted lowLevel (target : Uint256, amount : Uint256)
    local_obligations [low_level_frame := assumed "Raw EVM call, memory, and returndata choreography is an explicit refinement boundary."]
    : Uint256 := do
    memoryStore(0, amount)
    let pureRoundtrip := add (memoryLoad(0)) 0
    let roundtrip ← memoryLoad(0)
    let success ← evmCall(50000, target, amount, 0, 32, 64, 32)
    let observed ← evmStaticCall(50000, target, 0, 32, 64, 32)
    let size ← returnDataSize()
    returnDataCopy(96, 0, size)
    return (add (add (add pureRoundtrip roundtrip) success) observed)

  function reentrancy_trusted composedReturnDataSize ()
    local_obligations [low_level_frame := assumed "Reading returndata size is an explicit refinement boundary."]
    : Uint256 := do
    return (add (returnDataSize()) 1)

example : (ExternalCallInBodySmoke.linkedRead_modelBody).take 1 =
    [Compiler.CompilationModel.Stmt.externalCallBind
      ["depositable"] "getDepositableEther" []] := rfl

example : (ExternalCallInBodySmoke.linkedWrite_modelBody).take 1 =
    [Compiler.CompilationModel.Stmt.externalCallBind [] "deposit"
      [ .param "amount", .param "pubkey_data_offset", .param "pubkey_length" ]] := rfl

example : (ExternalCallInBodySmoke.lowLevel_modelBody).take 7 =
    [ Compiler.CompilationModel.Stmt.mstore (.literal 0) (.param "amount")
    , Compiler.CompilationModel.Stmt.letVar "pureRoundtrip" (.add (.mload (.literal 0)) (.literal 0))
    , Compiler.CompilationModel.Stmt.letVar "roundtrip" (.mload (.literal 0))
    , Compiler.CompilationModel.Stmt.letVar "success" (.call (.literal 50000) (.param "target") (.param "amount")
        (.literal 0) (.literal 32) (.literal 64) (.literal 32))
    , Compiler.CompilationModel.Stmt.letVar "observed" (.staticcall (.literal 50000) (.param "target")
        (.literal 0) (.literal 32) (.literal 64) (.literal 32))
    , Compiler.CompilationModel.Stmt.letVar "size" .returndataSize
    , Compiler.CompilationModel.Stmt.returndataCopy (.literal 96) (.literal 0) (.localVar "size") ] := rfl

example : ExternalCallInBodySmoke.linkedRead_model.body =
    ExternalCallInBodySmoke.linkedRead_modelBody :=
  ExternalCallInBodySmoke.linkedRead_semantic_preservation

example : ExternalCallInBodySmoke.linkedWrite_model.body =
    ExternalCallInBodySmoke.linkedWrite_modelBody :=
  ExternalCallInBodySmoke.linkedWrite_semantic_preservation

example : ExternalCallInBodySmoke.lowLevel_model.body =
    ExternalCallInBodySmoke.lowLevel_modelBody :=
  ExternalCallInBodySmoke.lowLevel_semantic_preservation

/-- error: unsupported expression in verity_contract body (see #1003 for planned macro support expansions) -/
#guard_msgs in
verity_contract MalformedEvmCallRejected where
  storage
  function bad (target : Uint256) : Uint256 := do
    return evmCall(1, target)

/-- error: callExternal 'scalarPair' expects 2 args, got 1 -/
#guard_msgs in
verity_contract MalformedLinkedCallRejected where
  storage
  linked_externals
    external scalarPair(Uint256, Uint256) -> (Uint256)
  function bad (payload : Bytes) : Uint256 := do
    let result ← callExternal scalarPair(payload)
    return result

/-- error: callExternal 'scalarPair' expects 2 args, got 1 -/
#guard_msgs in
verity_contract MalformedPureLinkedCallRejected where
  storage
  linked_externals
    external scalarPair(Uint256, Uint256) -> (Uint256)
  function bad (payload : Bytes) : Uint256 := do
    let result := callExternal scalarPair(payload)
    return result

/-- error: callExternal 'pair' return type expands to 2 values and cannot be bound to one source variable -/
#guard_msgs in
verity_contract CompositeLinkedCallBindRejected where
  storage
  linked_externals
    external pair(Uint256) -> (Tuple [Uint256, Uint256])
  function bad (value : Uint256) : Tuple [Uint256, Uint256] := do
    let result ← callExternal pair(value)
    return result

end Contracts.Smoke
