import Contracts.Smoke.StructMappings

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract ExternalCallSmoke where
  storage
    echoedValue : Uint256 := slot 0
  linked_externals
    external echo(Uint256) -> (Uint256)
    external echo_try(Uint256) -> (Bool, Uint256)

  function allow_post_interaction_writes reentrancy_trusted storeEcho (next : Uint256) : Unit := do
    let echoed := externalCall "echo" [next]
    setStorage echoedValue echoed

  function getEchoedValue () : Uint256 := do
    let current ← getStorage echoedValue
    return current

-- tryExternalCall smoke: single-return external with success flag (#1727, Axis 1 Step 5f)
verity_contract TryExternalCallSmoke where
  storage
    lastResult : Uint256 := slot 0
    callSucceeded : Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)
    external echo_try(Uint256) -> (Bool, Uint256)

  function allow_post_interaction_writes reentrancy_trusted tryEcho (x : Uint256) : Unit := do
    let (success, result) ← tryExternalCall "echo" [x]
    if success then
      setStorage lastResult result
      setStorage callSucceeded 1
    else
      setStorage callSucceeded 0

-- First-class Call.Result smoke: callers inspect the named result instead of
-- destructuring ad hoc `(success, value)` tuples (#1891).
verity_contract CallResultSmoke where
  storage
    lastResult : Uint256 := slot 0
    callSucceeded : Uint256 := slot 1
  linked_externals
    external echo(Uint256) -> (Uint256)
    external echo_try(Uint256) -> (Bool, Uint256)

  function allow_post_interaction_writes reentrancy_trusted storeCallResult (x : Uint256) : Unit := do
    let result ← callResult "echo" [x]
    if result.success then
      setStorage lastResult result.returndata
      setStorage callSucceeded 1
    else
      setStorage callSucceeded 0

example :
    CallResultSmoke.storeCallResult_modelBody.head? =
      some (Compiler.CompilationModel.Stmt.tryExternalCallBind
          "result_success"
          ["result_returndata"]
          "echo"
          [ Compiler.CompilationModel.Expr.param "x" ]) := rfl

example :
    (Contracts.callResultWords "echo" [7] :
      Contract (Contracts.Call.Result Uint256)).run
        defaultState =
      ContractResult.success
        { success := true, returndata := (7 : Uint256) }
        { defaultState with
            calls := [Contracts.linkedCallEntry "echo" [7] .success [7]]
            returndata := [7] } := by
  rfl

namespace StatefulExternalSmoke

open Compiler.ECM.StatefulExternal

private def world : ExternalWorld :=
  { accountState := fun address index => address + index }

private def request : Request :=
  { caller := 1
    target := 2
    selector := some 305419896
    calldata := [7]
    value := 0
    world := world }

private def balanceSummary : Summary :=
  { name := "balanceOf"
    selector := some 1889561905
    mutability := .staticcall
    assumptionNames := ["erc20_balanceOf_interface"] }

example :
    world = request.world := by
  have h :
      balanceSummary.interprets request (.success world [7]) := by
    simp [Summary.interprets, balanceSummary, request]
  have hsame :=
    Summary.static_success_preserves_world (summary := balanceSummary)
      (request := request) (world := world) (data := [7]) rfl h
  exact hsame

example :
    (Outcome.revert [1, 2, 3]).committedWorld? = none := by
  exact Summary.revert_has_no_committed_world [1, 2, 3]

end StatefulExternalSmoke

verity_contract LinkedExternalDynamicArgSmoke where
  storage
  linked_externals
    external hashArray(Array Uint256) -> (Uint256)
    external hashArray_try(Array Uint256) -> (Bool, Uint256)
    external notifyArray(Array Uint256)
    external hashBytes(Bytes) -> (Uint256)

  function reentrancy_trusted hashLeaves (leaves : Array Uint256) : Uint256 := do
    return externalCall "hashArray" [leaves]

  function reentrancy_trusted sendLeaves (leaves : Array Uint256) : Unit := do
    externalCallBind [] "notifyArray" [leaves]

  function reentrancy_trusted discardHash (leaves : Array Uint256) : Unit := do
    let _ := (externalCall "hashArray" [leaves] : Uint256)

  function reentrancy_trusted tryHash (leaves : Array Uint256) : Uint256 := do
    let (_success, h) ← tryExternalCall "hashArray" [leaves]
    return h

  function reentrancy_trusted hashPayload (payload : Bytes) : Uint256 := do
    return externalCall "hashBytes" [payload]

example :
    LinkedExternalDynamicArgSmoke.hashLeaves_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.externalCall
            "hashArray"
            [ Compiler.CompilationModel.Expr.param "leaves_data_offset"
            , Compiler.CompilationModel.Expr.param "leaves_length"
            ])
      ] := rfl

example :
    LinkedExternalDynamicArgSmoke.sendLeaves_modelBody =
      [ Compiler.CompilationModel.Stmt.externalCallBind
          []
          "notifyArray"
          [ Compiler.CompilationModel.Expr.param "leaves_data_offset"
          , Compiler.CompilationModel.Expr.param "leaves_length"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    LinkedExternalDynamicArgSmoke.discardHash_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "discard"
          (Compiler.CompilationModel.Expr.externalCall
            "hashArray"
            [ Compiler.CompilationModel.Expr.param "leaves_data_offset"
            , Compiler.CompilationModel.Expr.param "leaves_length"
            ])
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    LinkedExternalDynamicArgSmoke.tryHash_modelBody =
      [ Compiler.CompilationModel.Stmt.tryExternalCallBind
          "_success"
          ["h"]
          "hashArray"
          [ Compiler.CompilationModel.Expr.param "leaves_data_offset"
          , Compiler.CompilationModel.Expr.param "leaves_length"
          ]
      , Compiler.CompilationModel.Stmt.assignVar "_success"
          (.logicalNot (.eq (.localVar "_success") (.literal 0)))
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "h")
      ] := rfl

verity_contract LinkedExternalProjectedArrayArgSmoke where
  storage

  struct Transaction where
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    callData : Bytes

  linked_externals
    external hashArray(Array Uint256) -> (Uint256)
    external hashArray_try(Array Uint256) -> (Bool, Uint256)
    external hashBytes(Bytes) -> (Uint256)
    external hashBytes_try(Bytes) -> (Bool, Uint256)

  function reentrancy_trusted tryHashNullifiers (txs : Array Transaction, idx : Uint256) : Uint256 := do
    let (_success, h) ← tryExternalCall "hashArray" [(arrayElement txs idx).nullifierHashes]
    return h

  function reentrancy_trusted hashCallData (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return externalCall "hashBytes" [(arrayElement txs idx).callData]

  function reentrancy_trusted tryHashCallData (txs : Array Transaction, idx : Uint256) : Uint256 := do
    let (_success, h) ← tryExternalCall "hashBytes" [(arrayElement txs idx).callData]
    return h

example :
    LinkedExternalProjectedArrayArgSmoke.tryHashNullifiers_modelBody =
      [ Compiler.CompilationModel.Stmt.tryExternalCallBind
          "_success"
          ["h"]
          "hashArray"
          [ Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              1
          , Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              1
          ]
      , Compiler.CompilationModel.Stmt.assignVar "_success"
          (.logicalNot (.eq (.localVar "_success") (.literal 0)))
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "h")
      ] := rfl

example :
    LinkedExternalProjectedArrayArgSmoke.hashCallData_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.externalCall
            "hashBytes"
            [ Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                "txs"
                (Compiler.CompilationModel.Expr.param "idx")
                3
            , Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                "txs"
                (Compiler.CompilationModel.Expr.param "idx")
                3
            ])
      ] := rfl

example :
    LinkedExternalProjectedArrayArgSmoke.tryHashCallData_modelBody =
      [ Compiler.CompilationModel.Stmt.tryExternalCallBind
          "_success"
          ["h"]
          "hashBytes"
          [ Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              3
          , Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              3
          ]
      , Compiler.CompilationModel.Stmt.assignVar "_success"
          (.logicalNot (.eq (.localVar "_success") (.literal 0)))
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "h")
      ] := rfl

verity_contract NestedStructArrayProjectionSmoke where
  storage

  struct Proof where
    pA : FixedArray Uint256 2,
    pB : FixedArray (FixedArray Uint256 2) 2,
    pC : FixedArray Uint256 2

  struct Note where
    npk : Uint256,
    token : Address,
    amount : Uint256

  struct WithdrawalTransaction where
    proof : Proof,
    circuitId : Uint256,
    merkleRoot : Uint256,
    nullifierHashes : Array Uint256,
    newCommitments : Array Uint256,
    contextHash : Uint256,
    withdrawal : Note,
    ciphertexts : Array Uint256

  function withdrawalAmount (txs : Array WithdrawalTransaction, idx : Uint256) : Uint256 := do
    return (arrayElement txs idx).withdrawal.amount

  function consumeNullifiers (nullifiers : Array Uint256) : Unit := do
    let _len := arrayLength nullifiers
    pure ()

  function withdrawalAmountViaHelper (txs : Array WithdrawalTransaction, idx : Uint256) : Uint256 := do
    let amount ← withdrawalAmount txs idx
    return amount

  function consumeNullifiersViaHelper (txs : Array WithdrawalTransaction, idx : Uint256) : Unit := do
    consumeNullifiers (arrayElement txs idx).nullifierHashes

example :
    NestedStructArrayProjectionSmoke.withdrawalAmount_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElementDynamicWord
            "txs"
            (Compiler.CompilationModel.Expr.param "idx")
            15)
      ] := rfl

example :
    NestedStructArrayProjectionSmoke.withdrawalAmountViaHelper_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "amount"
          (Compiler.CompilationModel.Expr.internalCall
            "internal_withdrawalAmount"
            [ Compiler.CompilationModel.Expr.param "txs_data_offset"
            , Compiler.CompilationModel.Expr.param "txs_length"
            , Compiler.CompilationModel.Expr.param "idx"
            ])
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "amount")
      ] := rfl

example :
    NestedStructArrayProjectionSmoke.consumeNullifiersViaHelper_modelBody =
      [ Compiler.CompilationModel.Stmt.internalCall
          "internal_consumeNullifiers"
          [ Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              10
          , Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
              "txs"
              (Compiler.CompilationModel.Expr.param "idx")
              10
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

verity_contract DynamicStructElementHelperArgSmoke where
  storage

  struct Transaction where
    id : Uint256,
    values : Array Uint256

  function consumeValues (values : Array Uint256) : Uint256 := do
    return arrayLength values

  function inspect (txn : Transaction) : Uint256 := do
    let first := arrayElement txn.values 0
    let count ← consumeValues txn.values
    return add txn.id (add first count)

  function inspectAt (txs : Array Transaction, idx : Uint256) : Uint256 := do
    let total ← inspect (arrayElement txs idx)
    return total

example :
    DynamicStructElementHelperArgSmoke.inspect_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "first"
          (Compiler.CompilationModel.Expr.paramDynamicMemberElement
            "txn"
            1
            (Compiler.CompilationModel.Expr.literal 0))
      , Compiler.CompilationModel.Stmt.letVar
          "count"
          (Compiler.CompilationModel.Expr.internalCall
            "internal_consumeValues"
            [ Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset "txn" 1
            , Compiler.CompilationModel.Expr.paramDynamicMemberLength "txn" 1
            ])
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.add
            (Compiler.CompilationModel.Expr.paramDynamicHeadWord "txn" 0)
            (Compiler.CompilationModel.Expr.add
              (Compiler.CompilationModel.Expr.localVar "first")
              (Compiler.CompilationModel.Expr.localVar "count")))
      ] := rfl

example :
    DynamicStructElementHelperArgSmoke.inspectAt_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "total"
          (Compiler.CompilationModel.Expr.internalCall
            "internal_inspect"
            [ Compiler.CompilationModel.Expr.arrayElementDynamicDataOffset
                "txs"
                (Compiler.CompilationModel.Expr.param "idx")
            ])
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "total")
      ] := rfl

example :
    LinkedExternalDynamicArgSmoke.hashPayload_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.externalCall
            "hashBytes"
            [ Compiler.CompilationModel.Expr.param "payload_data_offset"
            , Compiler.CompilationModel.Expr.param "payload_length"
            ])
      ] := rfl

verity_contract ERC20HelperSmoke where
  storage
    lastBalance : Uint256 := slot 0
    lastAllowance : Uint256 := slot 1
    lastSupply : Uint256 := slot 2

  function pushTokens (token : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransfer token toAddr amount

  function pullTokens (token : Address, fromAddr : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransferFrom token fromAddr toAddr amount

  function approveTokens (token : Address, spender : Address, amount : Uint256) : Unit := do
    safeApprove token spender amount

  function allow_post_interaction_writes snapshotBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    setStorage lastBalance balance
    return balance

  function allow_post_interaction_writes snapshotAllowance (token : Address, owner : Address, spender : Address) : Uint256 := do
    let current ← allowance token owner spender
    setStorage lastAllowance current
    return current

  function allow_post_interaction_writes snapshotSupply (token : Address) : Uint256 := do
    let supply ← totalSupply token
    setStorage lastSupply supply
    return supply

verity_contract GenericECMReadSmoke where
  storage
    lastQuote : Uint256 := slot 0

  function allow_post_interaction_writes snapshotQuote (oracle : Address, asset : Address) : Uint256 := do
    let quote ← ecmCall
      (fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)
      [oracle, asset]
    setStorage lastQuote quote
    return quote

verity_contract GenericECMMultiResultSmoke where
  storage
    lastX : Uint256 := slot 0
    lastY : Uint256 := slot 1

  function allow_post_interaction_writes addPoints
      (x1 : Uint256, y1 : Uint256, x2 : Uint256, y2 : Uint256) : Unit := do
    ecmBind [sumX, sumY]
      (Compiler.Modules.Precompiles.bn256AddModule "sumX" "sumY")
      [x1, y1, x2, y2]
    setStorage lastX sumX
    setStorage lastY sumY

def genericECMTripleResultModule : Compiler.ECM.ExternalCallModule where
  name := "genericTripleResult"
  numArgs := 0
  resultVars := ["first", "second", "third"]
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

verity_contract GenericECMTripleResultSmoke where
  storage
    last : Uint256 := slot 0

  function allow_post_interaction_writes storeThird () : Unit := do
    ecmBind [first, second, third] genericECMTripleResultModule []
    setStorage last third

private def tripleResultAdversary :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ state => state
  result := fun _ _ => .success [1, 2, 3]
  gasUsed := fun _ _ => 0

/-- A read-only ECM still receives the caller-supplied adversary. -/
example :
    ((GenericECMTripleResultSmoke.storeThird tripleResultAdversary).run
      defaultState).getState.storage GenericECMTripleResultSmoke.last.slot = 3 := by
  decide

verity_contract GenericECMWriteSmoke where
  storage

  function runEffect (lhs : Uint256, rhs : Uint256) : Unit := do
    ecmDo genericECMEffectDemoModule [lhs, rhs]

example :
    ((GenericECMWriteSmoke.runEffect .stub 1 2).run defaultState).getState.calls.length = 1 := by
  native_decide

def directDynamicEcmResultModule (resultVar : String) : Compiler.ECM.ExternalCallModule where
  name := "directDynamicEcmResult"
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

def directDynamicEcmEffectModule : Compiler.ECM.ExternalCallModule where
  name := "directDynamicEcmEffect"
  numArgs := 2
  resultVars := []
  writesState := false
  readsState := false
  axioms := []
  compile := fun _ctx _args => pure []

verity_contract DirectDynamicECMArgSmoke where
  storage

  function fromCall (payload : Bytes) : Uint256 := do
    let result ← ecmCall directDynamicEcmResultModule [payload]
    return result

  function fromDo (message : String) : Unit := do
    ecmDo directDynamicEcmEffectModule [message]

  function fromBind (values : Array Uint256) : Unit := do
    ecmBind [result] (directDynamicEcmResultModule "result") [values]

private def successfulDynamicEcmAdversary :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site _ => .success (List.replicate site.returnArity 9)
  gasUsed := fun _ _ => 0

/-- Executable ECM calls use the same synthetic `data_offset, length` key as
the model for direct bytes, string, and dynamic-array parameters. -/
example :
    ((DirectDynamicECMArgSmoke.fromCall successfulDynamicEcmAdversary
      (ByteArray.mk #[1, 2, 3])).run defaultState).getState.calls.head?.map
        (fun call => call.calldata) = some [0, 3] := by
  decide

example :
    ((DirectDynamicECMArgSmoke.fromDo successfulDynamicEcmAdversary "verity").run
      defaultState).getState.calls.head?.map (fun call => call.calldata) = some [0, 6] := by
  decide

example :
    ((DirectDynamicECMArgSmoke.fromBind successfulDynamicEcmAdversary #[4, 5]).run
      defaultState).getState.calls.head?.map (fun call => call.calldata) = some [0, 2] := by
  decide

verity_contract BubblingValueCallECMSmoke where
  storage

  function forwardNoOutput (target : Address, ethValue : Uint256, inputOffset : Uint256, inputSize : Uint256) : Unit := do
    ecmDo Compiler.Modules.Calls.bubblingValueCallNoOutputModule
      [addressToWord target, ethValue, inputOffset, inputSize]

set_option linter.unusedVariables false in
verity_contract Create2SSTORE2Smoke where
  storage
    lastPointer : Address := slot 0

  function allow_post_interaction_writes reentrancy_trusted deploy (value : Uint256, initOffset : Uint256, initSize : Uint256, salt : Uint256) : Address := do
    let pointer ← ecmCall Compiler.Modules.Create2SSTORE2.deployModule
      [value, initOffset, initSize, salt]
    setStorageAddr lastPointer (wordToAddress pointer)
    return wordToAddress pointer

  function readCode (pointer : Address, destOffset : Uint256, codeOffset : Uint256, size : Uint256) : Unit := do
    ecmDo Compiler.Modules.Create2SSTORE2.readCodeModule
      [addressToWord pointer, destOffset, codeOffset, size]

set_option linter.unusedVariables false in
verity_contract CallbackABISmoke where
  storage

  function reentrancy_trusted onAction (target : Address, amount : Uint256, data : Bytes) : Unit := do
    ecmDo (Compiler.Modules.Callbacks.callbackModule 0x12345678 1 "data")
      [addressToWord target, amount]

set_option linter.unusedVariables false in
verity_contract CallWithValueSmoke where
  storage

  function reentrancy_trusted execute (target : Address, value : Uint256, dataOffset : Uint256, dataSize : Uint256) : Unit := do
    ecmDo Compiler.Modules.Calls.callWithValueModule [addressToWord target, value, dataOffset, dataSize]

  function reentrancy_trusted executeBytes (target : Address, value : Uint256, data : Bytes) : Unit := do
    ecmDo (Compiler.Modules.Calls.callWithValueBytesModule "data") [addressToWord target, value]

set_option linter.unusedVariables false in
verity_contract LowLevelTryCatchSmoke where
  storage
    lastOutcome : Uint256 := slot 0
  function allow_post_interaction_writes reentrancy_trusted catchFailure ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 1 0 0 0 0) (do
      setStorage lastOutcome 7)
    let current ← getStorage lastOutcome
    return current

  function allow_post_interaction_writes reentrancy_trusted skipCatchOnSuccess ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 1 0 0 0 0 0 0) (do
      setStorage lastOutcome 9)
    let current ← getStorage lastOutcome
    return current

  function allow_post_interaction_writes reentrancy_trusted catchFailureWithShadowedParam (verity_try_success : Uint256)
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 0 0 1 0 0 0 0) (do
      setStorage lastOutcome 11)
    let current ← getStorage lastOutcome
    return current

  function allow_post_interaction_writes reentrancy_trusted skipExternalCatchOnSuccess ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256
    := do
    tryCatch (call 1 0 0 0 0 0 0) (do
      let value ← evmCall(1, 0, 0, 0, 0, 0, 0)
      setStorage lastOutcome value)
    let current ← getStorage lastOutcome
    return current

/--
error: tryCatch catch payload 'err' is not available on the compilation-model path yet; use `_`/ignore it and read returndata explicitly if needed
-/
#guard_msgs in
verity_contract LowLevelTryCatchPayloadRejected where
  storage

  function badCatchPayload ()
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Unit
    := do
    tryCatch (call 0 0 0 0 0 0 0) (fun err => do
      require false err)

/--
error: ERC-20 helper form 'balanceOf' conflicts with contract function 'balanceOf'; rename the function or avoid the direct helper syntax here
-/
#guard_msgs in
verity_contract ERC20HelperShadowReadRejected where
  storage

  function balanceOf (token : Address, owner : Address) : Uint256 := do
    return (add (addressToWord token) (addressToWord owner))

  function readShadowedBalance (token : Address, owner : Address) : Uint256 := do
    let balance ← balanceOf token owner
    return balance

/--
error: ERC-20 helper form 'safeTransfer' conflicts with contract function 'safeTransfer'; rename the function or avoid the direct helper syntax here
-/
#guard_msgs in
verity_contract ERC20HelperShadowWriteRejected where
  storage
    lastTransfer : Uint256 := slot 0

  function safeTransfer (_token : Address, _to : Address, amount : Uint256) : Unit := do
    setStorage lastTransfer amount

  function writeShadowedTransfer (token : Address, toAddr : Address, amount : Uint256) : Unit := do
    safeTransfer token toAddr amount

/--
 error: linked external 'describe' uses unsupported return type; executable externalCall currently supports only word-like values and static ABI composites of word-like values
-/
#guard_msgs in
verity_contract ExternalCallUnsupportedType where
  storage
  linked_externals
    external describe(Uint256) -> (String)

  function noop () : Unit := do
    pure ()

-- Multi-return externals are now allowed (Step 5f); use tryExternalCall
-- to call them with a success flag.
verity_contract ExternalCallMultiReturn where
  storage
    lastValue : Uint256 := slot 0
  linked_externals
    external fanout(Uint256) -> (Uint256, Address)
    external fanout_try(Uint256) -> (Bool, Uint256, Address)

  function allow_post_interaction_writes reentrancy_trusted callFanout (x : Uint256) : Unit := do
    let (success, value, addr) ← tryExternalCall "fanout" [x]
    if success then
      setStorage lastValue value
      setStorage lastValue addr
    else
      pure ()

  function noop () : Unit := do
    pure ()

verity_contract ExternalCallTupleReturn where
  storage
  linked_externals
    external pair(Uint256) -> (Tuple [Uint256, Uint256])
    external pair_try(Uint256) -> (Bool, Tuple [Uint256, Uint256])

  function noop () : Unit := do
    pure ()

verity_contract ExternalCallTryWrapperMissingBoolRejected where
  storage
  linked_externals
    external pair(Uint256) -> (Uint256, Uint256)
    external pair_try(Uint256) -> (Uint256, Uint256, Uint256)

  function badTry (x : Uint256) : Uint256 := do
    let (_success, a, b) ← tryExternalCall "pair" [x]
    return add a b

/--
error: #check_contract failed for 'Contracts.Smoke.ExternalCallTryWrapperMissingBoolRejected': Compilation error: try wrapper 'pair_try' must return Bool followed by the flattened return values of external function 'pair'.
-/
#guard_msgs in
#check_contract ExternalCallTryWrapperMissingBoolRejected

/--
error: ecmDo requires an effect-only ECM module, but 'oracleReadUint256' binds 1 result value(s)
-/
#guard_msgs in
verity_contract GenericECMDoRejectsResultModules where
  storage

  function badEffect (oracle : Address) : Uint256 := do
    ecmDo (Compiler.Modules.Oracle.oracleReadUint256Module "quote" 0x12345678 0) [oracle]
    return 0

/--
error: ecmCall must elaborate to an ECM module binding exactly ['quote'], but 'genericEffectDemo' binds []
-/
#guard_msgs in
verity_contract GenericECMCallRejectsEffectOnlyModules where
  storage

  function badBind (lhs : Uint256, rhs : Uint256) : Uint256 := do
    let quote ← ecmCall (fun _ => genericECMEffectDemoModule) [lhs, rhs]
    return quote

/--
error: unsupported proof status 'pending'; expected proved, assumed, or unchecked
-/
#guard_msgs in
verity_contract LocalObligationRejectsUnknownStatus where
  storage

  function badStatus () local_obligations [manual_check := pending "Must be proved later."] : Unit := do
    pure ()

/--
error: duplicate local obligation 'manual_check' on function 'unsafeEdge'
-/
#guard_msgs in
verity_contract LocalObligationRejectsDuplicateNames where
  storage

  function unsafeEdge () local_obligations [manual_check := assumed "First localized trust boundary.", manual_check := unchecked "Second localized trust boundary."] : Unit := do
    pure ()

/--
error: constructor local obligation 'manual_check' must not be empty
-/
#guard_msgs in
verity_contract LocalObligationRejectsEmptyConstructorMessage where
  storage

  constructor () local_obligations [manual_check := unchecked ""] := do
    pure ()

  function noop () : Unit := do
    pure ()

verity_contract LocalObligationRequiredForUnsafeFunctionBoundary where
  storage

  function preview () : Uint256 := do
    let head := calldataload 0
    return head

/--
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeFunctionBoundary': Compilation error: function 'preview' uses low-level/assembly mechanic(s) calldataload outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract LocalObligationRequiredForUnsafeFunctionBoundary

verity_contract LocalObligationRequiredForUnsafeConstructorBoundary where
  storage

  constructor () := do
    mstore 0 1
    pure ()

  function noop () : Unit := do
    pure ()

/--
error: #check_contract failed for 'Contracts.Smoke.LocalObligationRequiredForUnsafeConstructorBoundary': Compilation error: constructor uses low-level/assembly mechanic(s) mstore outside an unsafe block without any local_obligations entry (Issue #1424 (controlled unsafe/assembly escape hatches)). Wrap the low-level code in `unsafe "reason" do` or add local_obligations [...] to make the trust boundary explicit.
-/
#guard_msgs in
#check_contract LocalObligationRequiredForUnsafeConstructorBoundary

/--
error: field 'approvals' is a nested struct mapping; use structMember2/setStructMember2
-/
#guard_msgs in
verity_contract StructMappingWrongReadAccessor where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember "approvals" owner "allowance"
    return amount

/--
error: field 'approvals' is a nested struct mapping; use structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongLegacyReadAccessor where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  function approvalOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← getMapping2 approvals owner spender
    return amount

/--
error: field 'positions' is not a nested struct mapping
-/
#guard_msgs in
verity_contract StructMappingWrongWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setStructMember2 "positions" owner owner "delegate" delegate_

/--
error: field 'positions' is a struct-valued mapping; use setStructMember
-/
#guard_msgs in
verity_contract StructMappingWrongLegacyWriteAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setDelegate (owner : Address, delegate_ : Address) : Unit := do
    setMapping2 positions owner owner delegate_

/--
error: unknown struct member 'nonce' on field 'positions'
-/
#guard_msgs in
verity_contract StructMappingUnknownMember where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function setNonce (owner : Address, value : Uint256) : Unit := do
    setStructMember "positions" owner "nonce" value

/--
error: field 'positions' is a struct-valued mapping; use structMember/structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongScalarReadAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function positionWord () : Uint256 := do
    let word ← getStorage positions
    return word

/--
error: field 'positions' is a struct-valued mapping; use structMember/structMember2
-/
#guard_msgs in
verity_contract StructMappingWrongScalarAddressReadAccessor where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function delegateWord () : Address := do
    let word ← getStorageAddr positions
    return word

/-! ### PR3 executable close-out: arity and failure continuation -/

private def arityAdversary (arity : Nat) (words : List Nat) :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ state => state
  result := fun site _ =>
    if site.returnArity = arity then .success words else .success []
  gasUsed := fun _ _ => 0

private def failAdv :
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel where
  stateTransition := fun _ state => state
  result := fun _ _ => .failure [5]
  gasUsed := fun _ _ => 0

/-- Declared arity 0: a successful empty payload continues as `(true, default)`. -/
example :
    (Contracts.tryExternalCallWords (α := Unit) "notifyBool" [1]
      (arityAdversary 0 []) 0 15).run defaultState =
      ContractResult.success (true, ())
        { defaultState with
            calls := [Contracts.linkedCallEntry "notifyBool" [1] .success [] 15]
            returndata := [] } := rfl

/-- Declared arity 2: both words are accepted; the helper no longer reverts
on a non-singleton payload. -/
example :
    (Contracts.tryExternalCallWords (α := Uint256) "dirtyPair" []
      (arityAdversary 2 [7, 9]) 2 6).run defaultState =
      ContractResult.success (true, (7 : Uint256))
        { defaultState with
            calls := [Contracts.linkedCallEntry "dirtyPair" [] .success [7, 9] 6]
            returndata := [7, 9] } := rfl

/-- Bound helpers auto-revert on adversary failure instead of fabricating 0. -/
example :
    (Contracts.externalCallContractWords (α := Uint256) "dirtyUint" [] failAdv 1 4).run
      defaultState =
      ContractResult.revert "external call failed" defaultState := rfl

/-- Bound helpers auto-revert when success returndata is shorter than arity. -/
example :
    (Contracts.externalCallContractWords (α := Uint256) "dirtyUint" []
      (arityAdversary 1 []) 1 4).run defaultState =
      ContractResult.revert "external call returned malformed data" defaultState := rfl

/-- Bound helpers decode the declared prefix and tolerate trailing returndata,
matching the compilation model's external-call binding semantics. -/
example :
    (Contracts.externalCallContractWords (α := Uint256) "dirtyUint" []
      (arityAdversary 1 [7, 9]) 1 4).run defaultState =
      ContractResult.success 7
        { defaultState with
            calls := [Contracts.linkedCallEntry "dirtyUint" [] .success [7, 9] 4]
            returndata := [7, 9] } := rfl

end Contracts.Smoke
