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
    external narrowEcho(Bytes4) -> (Uint256)
    external dirtyUint() -> (Uint32)
    external dirtyInt() -> (Int32)
    external dirtyBytes() -> (Bytes4)
    external dirtySink(Uint32) -> (Uint32)
    external consume(Uint256)

  function reentrancy_trusted linkedRead () : Uint256 := do
    let depositable ← callExternal getDepositableEther()
    return depositable

  function reentrancy_trusted linkedWrite (amount : Uint256, pubkey : Bytes) : Unit := do
    callExternal deposit(amount, pubkey)

  function reentrancy_trusted pureNarrow () : Uint256 := do
    let result := callExternal narrowEcho(0xdeadbeef)
    return result

  function reentrancy_trusted pureDirtyUint () : Uint32 := do
    let result := callExternal dirtyUint()
    return result

  function reentrancy_trusted directDirtyUint () : Uint32 := do
    return callExternal dirtyUint()

  function reentrancy_trusted nestedDirtyUint () : Bool := do
    return (callExternal dirtyUint()) == 1

  function reentrancy_trusted nestedExternalArg () : Uint32 := do
    return callExternal dirtySink(callExternal dirtyUint())

  function reentrancy_trusted storeDirtyUint ()
    local_obligations [low_level_frame := assumed "Writing a linked-call result to memory is an explicit refinement boundary."]
    : Unit := do
    memoryStore(0, callExternal dirtyUint())

  function reentrancy_trusted bindDirtyUint () : Uint32 := do
    let result ← callExternal dirtyUint()
    return result

  function reentrancy_trusted bindNestedExternalArg () : Uint32 := do
    let result ← callExternal dirtySink(callExternal dirtyUint())
    return result

  function reentrancy_trusted statementNestedExternalArg () : Unit := do
    callExternal consume(callExternal narrowEcho(0xdeadbeef))

  function reentrancy_trusted logDirtyUint ()
    local_obligations [low_level_frame := assumed "Logging a linked-call result is an explicit refinement boundary."]
    : Unit := do
    rawLog [callExternal dirtyUint()] 0 0

  function reentrancy_trusted pureDirtyInt () : Int32 := do
    let result := callExternal dirtyInt()
    return result

  function reentrancy_trusted bindDirtyInt () : Int32 := do
    let result ← callExternal dirtyInt()
    return result

  function reentrancy_trusted pureDirtyBytes () : Bytes4 := do
    let result := callExternal dirtyBytes()
    return result

  function reentrancy_trusted bindDirtyBytes () : Bytes4 := do
    let result ← callExternal dirtyBytes()
    return result

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

  function reentrancy_trusted discardedReturnDataSize ()
    local_obligations [low_level_frame := assumed "Reading returndata size is an explicit refinement boundary."]
    : Uint256 := do
    let _ ← returnDataSize()
    let _ ← (returnDataSize())
    let parenthesized ← (returnDataSize())
    return parenthesized

example : (ExternalCallInBodySmoke.linkedRead_modelBody).take 1 =
    [Compiler.CompilationModel.Stmt.externalCallBind
      ["depositable"] "getDepositableEther" []] := rfl

example : (ExternalCallInBodySmoke.linkedWrite_modelBody).take 1 =
    [Compiler.CompilationModel.Stmt.externalCallBind [] "deposit"
      [ .param "amount", .param "pubkey_data_offset", .param "pubkey_length" ]] := rfl

example : (ExternalCallInBodySmoke.pureNarrow_modelBody).take 1 =
    [Compiler.CompilationModel.Stmt.letVar "result"
      (.externalCall "narrowEcho" [
        .literal 100720434702924942364018397558880508427273416251376888068364465368051161759744])] := rfl

example : ExternalCallInBodySmoke.pureNarrow_model.body =
    ExternalCallInBodySmoke.pureNarrow_modelBody :=
  ExternalCallInBodySmoke.pureNarrow_semantic_preservation

example : (ExternalCallInBodySmoke.pureDirtyUint_modelBody).take 1 =
    [.letVar "result" (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))] := rfl

example : ExternalCallInBodySmoke.directDirtyUint_modelBody =
    [.return (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))] := rfl

example : ExternalCallInBodySmoke.nestedDirtyUint_modelBody =
    [.return (.eq
      (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))
      (.literal 1))] := rfl

example : ExternalCallInBodySmoke.nestedExternalArg_modelBody =
    [.return (.bitAnd
      (.externalCall "dirtySink"
        [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))])
      (.literal (2 ^ 32 - 1)))] := rfl

example : ExternalCallInBodySmoke.storeDirtyUint_modelBody =
    [.mstore (.literal 0)
      (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))] := rfl

example : (ExternalCallInBodySmoke.bindDirtyUint_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyUint" []
    , .assignVar "result" (.bitAnd (.localVar "result") (.literal (2 ^ 32 - 1))) ] := rfl

example : (ExternalCallInBodySmoke.bindNestedExternalArg_modelBody).take 1 =
    [.externalCallBind ["result"] "dirtySink"
      [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))]] := rfl

example : ExternalCallInBodySmoke.statementNestedExternalArg_modelBody =
    [.externalCallBind [] "consume"
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])]] := rfl

example : ExternalCallInBodySmoke.logDirtyUint_modelBody =
    [.rawLog [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))]
      (.literal 0) (.literal 0)] := rfl

example : (ExternalCallInBodySmoke.pureDirtyInt_modelBody).take 1 =
    [.letVar "result" (.signextend (.literal 3) (.externalCall "dirtyInt" []))] := rfl

example : (ExternalCallInBodySmoke.bindDirtyInt_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyInt" []
    , .assignVar "result" (.signextend (.literal 3) (.localVar "result")) ] := rfl

example : (ExternalCallInBodySmoke.pureDirtyBytes_modelBody).take 1 =
    [.letVar "result" (.bitAnd (.externalCall "dirtyBytes" [])
      (.literal ((2 ^ 32 - 1) * 2 ^ 224)))] := rfl

example : (ExternalCallInBodySmoke.bindDirtyBytes_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyBytes" []
    , .assignVar "result" (.bitAnd (.localVar "result")
        (.literal ((2 ^ 32 - 1) * 2 ^ 224))) ] := rfl

example : ExternalCallInBodySmoke.pureDirtyUint_model.body =
    ExternalCallInBodySmoke.pureDirtyUint_modelBody :=
  ExternalCallInBodySmoke.pureDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.directDirtyUint_model.body =
    ExternalCallInBodySmoke.directDirtyUint_modelBody :=
  ExternalCallInBodySmoke.directDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.nestedDirtyUint_model.body =
    ExternalCallInBodySmoke.nestedDirtyUint_modelBody :=
  ExternalCallInBodySmoke.nestedDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.nestedExternalArg_model.body =
    ExternalCallInBodySmoke.nestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.nestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.storeDirtyUint_model.body =
    ExternalCallInBodySmoke.storeDirtyUint_modelBody :=
  ExternalCallInBodySmoke.storeDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.bindDirtyUint_model.body =
    ExternalCallInBodySmoke.bindDirtyUint_modelBody :=
  ExternalCallInBodySmoke.bindDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.bindNestedExternalArg_model.body =
    ExternalCallInBodySmoke.bindNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.bindNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.statementNestedExternalArg_model.body =
    ExternalCallInBodySmoke.statementNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.statementNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.logDirtyUint_model.body =
    ExternalCallInBodySmoke.logDirtyUint_modelBody :=
  ExternalCallInBodySmoke.logDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.pureDirtyInt_model.body =
    ExternalCallInBodySmoke.pureDirtyInt_modelBody :=
  ExternalCallInBodySmoke.pureDirtyInt_semantic_preservation

example : ExternalCallInBodySmoke.bindDirtyInt_model.body =
    ExternalCallInBodySmoke.bindDirtyInt_modelBody :=
  ExternalCallInBodySmoke.bindDirtyInt_semantic_preservation

example : ExternalCallInBodySmoke.pureDirtyBytes_model.body =
    ExternalCallInBodySmoke.pureDirtyBytes_modelBody :=
  ExternalCallInBodySmoke.pureDirtyBytes_semantic_preservation

example : ExternalCallInBodySmoke.bindDirtyBytes_model.body =
    ExternalCallInBodySmoke.bindDirtyBytes_modelBody :=
  ExternalCallInBodySmoke.bindDirtyBytes_semantic_preservation

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

example : (ExternalCallInBodySmoke.discardedReturnDataSize_modelBody).take 3 =
    [ Compiler.CompilationModel.Stmt.letVar "__discard" .returndataSize
    , Compiler.CompilationModel.Stmt.letVar "__discard_1" .returndataSize
    , Compiler.CompilationModel.Stmt.letVar "parenthesized" .returndataSize ] := rfl

example : ExternalCallInBodySmoke.discardedReturnDataSize_model.body =
    ExternalCallInBodySmoke.discardedReturnDataSize_modelBody :=
  ExternalCallInBodySmoke.discardedReturnDataSize_semantic_preservation

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

/-- error: callExternal 'pair' return type cannot be used as a pure single-word expression -/
#guard_msgs in
verity_contract CompositePureLinkedCallRejected where
  storage
  linked_externals
    external pair(Uint256) -> (Tuple [Uint256, Uint256])
  function bad (value : Uint256) : Tuple [Uint256, Uint256] := do
    let result := callExternal pair(value)
    return result

/-- error: memory-store value requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got Verity.Macro.ValueType.bytes -/
#guard_msgs in
verity_contract DynamicMemoryStoreRejected where
  storage
  function bad (payload : Bytes) : Unit := do
    memoryStore(0, payload)

/-- error: returndata-copy destination offset requires a word-like value (Uint256, Int256, Uint8, Address, or Bytes32), got Verity.Macro.ValueType.bytes -/
#guard_msgs in
verity_contract DynamicReturnDataCopyRejected where
  storage
  function bad (payload : Bytes) : Unit := do
    returnDataCopy(payload, 0, 32)

end Contracts.Smoke
