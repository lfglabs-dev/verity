import Contracts.Common

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def linkedOperandEcmModule : Compiler.ECM.ExternalCallModule where
  name := "linkedOperandEcm"
  numArgs := 1
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

def linkedWordPassthrough (value : Uint256) : Uint256 := value

-- P0 #1003 coverage for linked calls and explicit low-level body syntax.
-- `callExternal` is declaration-driven; target/value fields belong to `evmCall`.
verity_contract ExternalCallInBodySmoke where
  storage
    values : Uint256 → Uint256 := slot 0
  struct NarrowPair where
    narrow : Uint32,
    wide : Uint256
  errors
    error Failure(Uint256)

  linked_externals
    external getDepositableEther() -> (Uint256)
    external deposit(Uint256, Bytes)
    external narrowEcho(Bytes4) -> (Uint256)
    external dirtyUint() -> (Uint32)
    external dirtyUint_try() -> (Bool, Uint32)
    external dirtyPair() -> (NarrowPair)
    external dirtyPair_try() -> (Bool, NarrowPair)
    external dirtyInt() -> (Int32)
    external dirtyBytes() -> (Bytes4)
    external dirtyAddress() -> (Address)
    external dirtyBool() -> (Bool)
    external dirtySink(Uint32) -> (Uint32)
    external consumeUint8(Uint8)
    external consumeUint16(Uint16)
    external consume(Uint256)
    external notifyBool(Bool)
    external notifyBool_try(Bool) -> (Bool)
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

  function reentrancy_trusted tryDirtyUint () : Uint32 := do
    let (_success, result) ← tryExternalCall "dirtyUint" []
    return result

  function reentrancy_trusted callResultDirtyUint () : Uint32 := do
    let result ← callResult "dirtyUint" []
    return result.returndata

  function reentrancy_trusted tryNotifyBool (flag : Bool) : Bool := do
    let success ← tryExternalCall "notifyBool" [flag]
    return success

  function reentrancy_trusted tryDirtyPair () : Uint32 := do
    let (_success, result) ← tryExternalCall "dirtyPair" []
    return result.narrow

  function reentrancy_trusted bindDirtyAddress () : Address := do
    let result ← callExternal dirtyAddress()
    return result

  function reentrancy_trusted bindDirtyBool () : Bool := do
    let result ← callExternal dirtyBool()
    return result

  function reentrancy_trusted leanHelperNestedExternal () : Uint256 := do
    return linkedWordPassthrough (callExternal narrowEcho(0xdeadbeef))

  function reentrancy_trusted bindNestedExternalArg () : Uint32 := do
    let result ← callExternal dirtySink(callExternal dirtyUint())
    return result

  function reentrancy_trusted statementNestedExternalArg () : Unit := do
    callExternal consume(callExternal narrowEcho(0xdeadbeef))

  function reentrancy_trusted logDirtyUint ()
    local_obligations [low_level_frame := assumed "Logging a linked-call result is an explicit refinement boundary."]
    : Unit := do
    rawLog [callExternal dirtyUint()] 0 0

  function reentrancy_trusted legacyNarrowArgs () : Unit := do
    callExternal consumeUint8(0x100)
    callExternal consumeUint16(0x10000)

  function reentrancy_trusted emitNestedExternalArg () : Unit := do
    emit "Seen" [callExternal narrowEcho(0xdeadbeef)]

  function reentrancy_trusted customErrorNestedExternalArg () : Unit := do
    requireError true Failure(callExternal narrowEcho(0xdeadbeef))

  function consumeHelper (_value : Uint256) : Unit := do
    pure ()

  function reentrancy_trusted helperNestedExternalArg () : Unit := do
    consumeHelper (callExternal narrowEcho(0xdeadbeef))

  function reentrancy_trusted monadicLoadDirtyUint ()
    local_obligations [low_level_frame := assumed "Reading memory through a linked-call offset is an explicit refinement boundary."]
    : Uint256 := do
    let value ← memoryLoad(callExternal dirtyUint())
    return value

  function reentrancy_trusted ecmNestedExternalArg () : Unit := do
    ecmDo linkedOperandEcmModule [callExternal narrowEcho(0xdeadbeef)]

  function reentrancy_trusted erc20BalanceNestedExternalArg () : Uint256 := do
    let result ← balanceOf 1 (callExternal narrowEcho(0xdeadbeef))
    return result

  function reentrancy_trusted erc20AllowanceNestedExternalArg () : Uint256 := do
    let result ← allowance 1 2 (callExternal narrowEcho(0xdeadbeef))
    return result

  function reentrancy_trusted erc20SupplyNestedExternalArg () : Uint256 := do
    let result ← totalSupply (callExternal narrowEcho(0xdeadbeef))
    return result

  function reentrancy_trusted mappingNestedExternalArg () : Uint256 := do
    let result ← getMappingUint values (callExternal narrowEcho(0xdeadbeef))
    return result

  function reentrancy_trusted tupleNestedExternalResult () : Uint32 := do
    let (result, _) := (callExternal dirtyUint(), 0)
    return result

  function reentrancy_trusted tupleNestedExternalReturn () : Tuple [Uint32, Uint256] := do
    return (callExternal dirtyUint(), 0)

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

verity_contract AdtLinkedPayloadSmoke where
  inductive
    Maybe := | Nothing | Just(value : Uint32)
  storage
    result : Maybe := slot 0
  linked_externals
    external dirtyUint() -> (Uint32)
  function store () : Unit := do
    setStorage result (adt "Just" [callExternal dirtyUint()])

example : (AdtLinkedPayloadSmoke.store_modelBody).take 1 =
    [.setStorage "result" (.adtConstruct "Maybe" "Just"
      [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))])] := rfl

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
        [(.bitAnd
          (.bitAnd (.externalCall "dirtyUint" []) (.literal 4294967295))
          (.literal 4294967295))])
      (.literal 4294967295))] := rfl

example : ExternalCallInBodySmoke.storeDirtyUint_modelBody =
    [.mstore (.literal 0)
      (.bitAnd (.externalCall "dirtyUint" []) (.literal 4294967295)), .stop] := rfl

example : (ExternalCallInBodySmoke.bindDirtyUint_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyUint" []
    , .assignVar "result" (.bitAnd (.localVar "result") (.literal (2 ^ 32 - 1))) ] := rfl

example : (ExternalCallInBodySmoke.tryDirtyUint_modelBody).take 2 =
    [ .tryExternalCallBind "_success" ["result"] "dirtyUint" []
    , .assignVar "_success" (.logicalNot (.eq (.localVar "_success") (.literal 0))) ] := rfl

example : (ExternalCallInBodySmoke.callResultDirtyUint_modelBody).take 3 =
    [ .tryExternalCallBind "result_success" ["result_returndata"] "dirtyUint" []
    , .assignVar "result_success"
        (.logicalNot (.eq (.localVar "result_success") (.literal 0)))
    , .assignVar "result_returndata"
        (.bitAnd (.localVar "result_returndata") (.literal (2 ^ 32 - 1))) ] := rfl

example : (ExternalCallInBodySmoke.tryNotifyBool_modelBody).take 2 =
    [.tryExternalCallBind "success" [] "notifyBool"
      [(.logicalNot (.eq (.param "flag") (.literal 0)))],
     .assignVar "success" (.logicalNot (.eq (.localVar "success") (.literal 0)))] := rfl

example : (ExternalCallInBodySmoke.tryDirtyPair_modelBody).take 4 =
    [ .tryExternalCallBind "_success" ["result_narrow", "result_wide"] "dirtyPair" []
    , .assignVar "_success" (.logicalNot (.eq (.localVar "_success") (.literal 0)))
    , .assignVar "result_narrow"
        (.bitAnd (.localVar "result_narrow") (.literal (2 ^ 32 - 1)))
    , .return (.localVar "result_narrow") ] := rfl

example : (ExternalCallInBodySmoke.bindDirtyAddress_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyAddress" []
    , .assignVar "result" (.bitAnd (.localVar "result") (.literal (2 ^ 160 - 1))) ] := rfl

example : (ExternalCallInBodySmoke.bindDirtyBool_modelBody).take 2 =
    [ .externalCallBind ["result"] "dirtyBool" []
    , .assignVar "result" (.logicalNot (.eq (.localVar "result") (.literal 0))) ] := rfl

example : ExternalCallInBodySmoke.leanHelperNestedExternal_modelBody =
    [.return (.externalCall "narrowEcho"
      [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])] := rfl

example : (ExternalCallInBodySmoke.bindNestedExternalArg_modelBody).take 1 =
    [.externalCallBind ["result"] "dirtySink"
      [(.bitAnd
        (.bitAnd (.externalCall "dirtyUint" []) (.literal 4294967295))
        (.literal 4294967295))]] := rfl

example : ExternalCallInBodySmoke.statementNestedExternalArg_modelBody =
    [.externalCallBind [] "consume"
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])],
      .stop] := rfl

example : ExternalCallInBodySmoke.logDirtyUint_modelBody =
    [.rawLog [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1)))]
      (.literal 0) (.literal 0), .stop] := rfl

example : ExternalCallInBodySmoke.legacyNarrowArgs_modelBody =
    [ .externalCallBind [] "consumeUint8" [(.bitAnd (.literal 0x100) (.literal 255))]
    , .externalCallBind [] "consumeUint16" [(.bitAnd (.literal 0x10000) (.literal 65535))]
    , .stop ] := rfl

example : ExternalCallInBodySmoke.emitNestedExternalArg_modelBody =
    [.emit "Seen"
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])],
      .stop] := rfl

example : ExternalCallInBodySmoke.customErrorNestedExternalArg_modelBody =
    [.requireError (.literal 1) "Failure"
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])],
      .stop] := rfl

example : ExternalCallInBodySmoke.helperNestedExternalArg_modelBody =
    [.internalCall "internal_consumeHelper"
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])],
      .stop] := rfl

example : (ExternalCallInBodySmoke.monadicLoadDirtyUint_modelBody).take 1 =
    [.letVar "value" (.mload
      (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1))))] := rfl

example : ExternalCallInBodySmoke.ecmNestedExternalArg_modelBody =
    [.ecm linkedOperandEcmModule
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])],
      .stop] := rfl

example : (ExternalCallInBodySmoke.erc20BalanceNestedExternalArg_modelBody).take 1 =
    [.ecm (Compiler.Modules.ERC20.balanceOfModule "result")
      [(.literal 1), (.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])]] := rfl

example : (ExternalCallInBodySmoke.erc20AllowanceNestedExternalArg_modelBody).take 1 =
    [.ecm (Compiler.Modules.ERC20.allowanceModule "result")
      [(.literal 1), (.literal 2), (.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])]] := rfl

example : (ExternalCallInBodySmoke.erc20SupplyNestedExternalArg_modelBody).take 1 =
    [.ecm (Compiler.Modules.ERC20.totalSupplyModule "result")
      [(.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)])]] := rfl

example : (ExternalCallInBodySmoke.mappingNestedExternalArg_modelBody).take 1 =
    [.letVar "result" (.mappingUint "values"
      (.externalCall "narrowEcho"
        [(.literal 100720434702924942364018397558880508427273416251376888068364465368051161759744)]))] := rfl

example : ExternalCallInBodySmoke.mappingNestedExternalArg_model.body =
    ExternalCallInBodySmoke.mappingNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.mappingNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.tupleNestedExternalResult_modelBody =
    [.letVar "result" (.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1))),
     .return (.localVar "result")] := rfl

example : ExternalCallInBodySmoke.tupleNestedExternalReturn_modelBody =
    [.returnValues [(.bitAnd (.externalCall "dirtyUint" []) (.literal (2 ^ 32 - 1))), .literal 0]] := rfl

example : ExternalCallInBodySmoke.legacyNarrowArgs_model.body =
    ExternalCallInBodySmoke.legacyNarrowArgs_modelBody :=
  ExternalCallInBodySmoke.legacyNarrowArgs_semantic_preservation

example : ExternalCallInBodySmoke.emitNestedExternalArg_model.body =
    ExternalCallInBodySmoke.emitNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.emitNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.customErrorNestedExternalArg_model.body =
    ExternalCallInBodySmoke.customErrorNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.customErrorNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.helperNestedExternalArg_model.body =
    ExternalCallInBodySmoke.helperNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.helperNestedExternalArg_semantic_preservation

example : ExternalCallInBodySmoke.monadicLoadDirtyUint_model.body =
    ExternalCallInBodySmoke.monadicLoadDirtyUint_modelBody :=
  ExternalCallInBodySmoke.monadicLoadDirtyUint_semantic_preservation

example : ExternalCallInBodySmoke.ecmNestedExternalArg_model.body =
    ExternalCallInBodySmoke.ecmNestedExternalArg_modelBody :=
  ExternalCallInBodySmoke.ecmNestedExternalArg_semantic_preservation

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

/-- error: callExternal 'pair' return type cannot be bound to one source variable; bind composite results explicitly -/
#guard_msgs in
verity_contract CompositeLinkedCallBindRejected where
  storage
  linked_externals
    external pair(Uint256) -> (Tuple [Uint256, Uint256])
  function bad (value : Uint256) : Tuple [Uint256, Uint256] := do
    let result ← callExternal pair(value)
    return result

/-- error: callExternal 'single' return type cannot be bound to one source variable; bind composite results explicitly -/
#guard_msgs in
verity_contract SingleLeafCompositeLinkedCallBindRejected where
  storage
  struct Single where
    value : Uint256
  linked_externals
    external single() -> (Single)
  function bad () : Single := do
    let result ← callExternal single()
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

/-- error: requireSomeUint operands cannot contain callExternal because safe-arithmetic lowering reuses operands in both the guard and result; bind the external result first -/
#guard_msgs in
verity_contract EffectfulSafeArithmeticOperandRejected where
  storage
  linked_externals
    external dirtyUint() -> (Uint32)
  function bad () : Uint256 := do
    let result ← requireSomeUint (safeAdd (callExternal dirtyUint()) 1) "overflow"
    return result

/-- error: conditional operands cannot contain callExternal because expression lowering duplicates the condition and evaluates both branches; use statement-level control flow -/
#guard_msgs in
verity_contract EffectfulConditionalBranchRejected where
  storage
  linked_externals
    external dirtyUint() -> (Uint32)
  function bad (flag : Bool) : Uint32 := do
    return ite flag (callExternal dirtyUint()) 0

/-- error: conditional operands cannot contain callExternal because expression lowering duplicates the condition and evaluates both branches; use statement-level control flow -/
#guard_msgs in
verity_contract EffectfulConditionalConditionRejected where
  storage
  linked_externals
    external dirtyBool() -> (Bool)
  function bad () : Uint256 := do
    return ite (callExternal dirtyBool()) 1 0

/-- error: duplicated expression operands cannot contain callExternal; bind the external result first -/
#guard_msgs in
verity_contract EffectfulDuplicatedOperandRejected where
  storage
  linked_externals
    external dirtyUint() -> (Uint32)
  function bad () : Uint256 := do
    return min (callExternal dirtyUint()) 1

/-- error: tryExternalCall 'dirtyPair' flattened result variable 'result_narrow' conflicts with an existing local -/
#guard_msgs in
verity_contract FlattenedTryResultCollisionRejected where
  storage
  struct NarrowPair where
    narrow : Uint32,
    wide : Uint256
  linked_externals
    external dirtyPair() -> (NarrowPair)
  function bad () : Uint32 := do
    let result_narrow := 7
    let (_success, result) ← tryExternalCall "dirtyPair" []
    return result.narrow

/-- error: short-circuit logical operands cannot contain callExternal because expression lowering evaluates both operands; bind the external result first -/
#guard_msgs in
verity_contract EffectfulShortCircuitOperandRejected where
  storage
  linked_externals
    external dirtyBool() -> (Bool)
  function bad (flag : Bool) : Bool := do
    return flag && callExternal dirtyBool()

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
