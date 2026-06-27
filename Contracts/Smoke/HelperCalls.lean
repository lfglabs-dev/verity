import Contracts.Smoke.StructsAndArrays

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract LeanDefHelperSmoke where
  storage

  function addOffset (x : Uint256, y : Int256) : Uint256 := do
    return (plusInt256Helper x y)

  function sameWord (x : Uint256, y : Uint256) : Uint256 := do
    return (eqWordHelper x y)

def leanDefHelperExecutableAddsPositiveOffset : Bool :=
  match LeanDefHelperSmoke.addOffset 10 3 Verity.defaultState with
  | .success value _ => value == 13
  | _ => false

example : leanDefHelperExecutableAddsPositiveOffset = true := by decide

def leanDefHelperExecutableUsesEquality : Bool :=
  match LeanDefHelperSmoke.sameWord 7 7 Verity.defaultState with
  | .success value _ => value == 1
  | _ => false

example : leanDefHelperExecutableUsesEquality = true := by decide

verity_contract DirectHelperCallSmoke where
  storage
    total : Uint256 := slot 0
    lastLeft : Uint256 := slot 1
    lastRight : Uint256 := slot 2

  function addToTotal (amount : Uint256) : Unit := do
    let current ← getStorage total
    setStorage total (add current amount)

  function readTotalPlus (extra : Uint256) : Uint256 := do
    let current ← getStorage total
    return (add current extra)

  function pairWithTotal (offset : Uint256) : Tuple [Uint256, Uint256] := do
    let current ← getStorage total
    return (current, add current offset)

  function allow_post_interaction_writes runHelpers (amount : Uint256, extra : Uint256, offset : Uint256) : Uint256 := do
    addToTotal amount
    let combined ← readTotalPlus extra
    let (left, right) ← pairWithTotal offset
    setStorage lastLeft left
    setStorage lastRight right
    return combined

  function snapshot () : Tuple [Uint256, Uint256, Uint256] := do
    let current ← getStorage total
    let left ← getStorage lastLeft
    let right ← getStorage lastRight
    return (current, left, right)

verity_contract MultiReturnHelperSmoke where
  storage
    lastTotal : Uint256 := slot 0
    lastHead : Uint256 := slot 1

  function summarize (seed : Uint256) : Tuple [Uint256, Uint256] := do
    let head := add seed 1
    let tail := add seed 2
    return (head, tail)

  function useSummary (seed : Uint256) : Uint256 := do
    let (head, tail) ← summarize seed
    return (add head tail)

verity_contract ArrayHelperCallSmoke where
  storage
    ok : Uint256 := slot 0

  function first (xs : Array Uint256) : Uint256 := do
    return arrayElement xs 0

  function allow_post_interaction_writes useFirst (xs : Array Uint256) : Unit := do
    let x ← first xs
    setStorage ok x

example :
    ArrayHelperCallSmoke.first_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.arrayElement
            "xs"
            (Compiler.CompilationModel.Expr.literal 0))
      ] := rfl

example :
    ArrayHelperCallSmoke.useFirst_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "x"
          (Compiler.CompilationModel.Expr.internalCall
            "internal_first"
            [ Compiler.CompilationModel.Expr.param "xs_data_offset"
            , Compiler.CompilationModel.Expr.param "xs_length"
            ])
      , Compiler.CompilationModel.Stmt.setStorage
          "ok"
          (Compiler.CompilationModel.Expr.localVar "x")
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (emit "Batch" [(returnArray #[(1 : Uint256), 2, 3] : Contract (Array Uint256))]
        |>.run Verity.defaultState).getState.events =
      [{ name := "Batch", args := [3], indexedArgs := [] }] := rfl

verity_contract ForEachMutableLocalSmoke where
  storage
    seen : Uint256 := slot 0

  function sumValues (values : Array Uint256) : Uint256 := do
    let mut total := 0
    forEach "i" (arrayLength values) (do
      let value := arrayElement values i
      total := add total value)
    return total

  function allow_post_interaction_writes reentrancy_trusted sumOnCatch (values : Array Uint256)
    local_obligations [manual_low_level_refinement := assumed "Low-level call success/failure boundary still requires a manual refinement argument."]
    : Uint256 := do
    tryCatch (call 0 0 1 0 0 0 0) (do
      forEach "i" (arrayLength values) (do
        let value := arrayElement values i
        setStorage seen value))
    let current ← getStorage seen
    return current

  function sumUnsafe (values : Array Uint256) : Uint256 := do
    let mut total := 0
    unsafe "test: nested forEach binder in executable unsafe block" do
      forEach "i" (arrayLength values) (do
        let value := arrayElement values i
        total := add total value)
    return total

example :
    ForEachMutableLocalSmoke.sumValues_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "total"
          (Compiler.CompilationModel.Expr.literal 0)
      , Compiler.CompilationModel.Stmt.forEach "i"
          (Compiler.CompilationModel.Expr.arrayLength "values")
          [ Compiler.CompilationModel.Stmt.letVar "value"
              (Compiler.CompilationModel.Expr.arrayElement "values"
                (Compiler.CompilationModel.Expr.localVar "i"))
          , Compiler.CompilationModel.Stmt.assignVar "total"
              (Compiler.CompilationModel.Expr.add
                (Compiler.CompilationModel.Expr.localVar "total")
                (Compiler.CompilationModel.Expr.localVar "value"))
          ]
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "total")
      ] := rfl

verity_contract DirectHelperCallBytesEffectSmoke where
  storage

  function consumePayload (_payload : Bytes) : Unit := do
    pure ()

  function run (payload : Bytes) : Unit := do
    consumePayload payload

verity_contract DirectHelperCallBytesBindSmoke where
  storage

  function samePayload (lhs : Bytes, rhs : Bytes) : Bool := do
    return (lhs == rhs)

  function run (payload : Bytes) : Bool := do
    let same ← samePayload payload payload
    return same

verity_contract DirectHelperCallBytesTupleSmoke where
  storage

  function fanoutPayload (_payload : Bytes) : Tuple [Uint256, Uint256] := do
    return (0, 1)

  function run (payload : Bytes) : Tuple [Uint256, Uint256] := do
    let (left, right) ← fanoutPayload payload
    return (left, right)

verity_contract DirectHelperCallProjectedBytesArgSmoke where
  storage

  struct Operation where
    sender : Address,
    callData : Bytes,
    nonce : Uint256

  function consumePayload (_payload : Bytes) : Uint256 := do
    return 1

  function run (ops : Array Operation, idx : Uint256) : Uint256 := do
    let count ← consumePayload (arrayElement ops idx).callData
    return count

example :
    DirectHelperCallProjectedBytesArgSmoke.run_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "count"
          (Compiler.CompilationModel.Expr.internalCall
            "internal_consumePayload"
            [ Compiler.CompilationModel.Expr.arrayElementDynamicMemberDataOffset
                "ops"
                (Compiler.CompilationModel.Expr.param "idx")
                1
            , Compiler.CompilationModel.Expr.arrayElementDynamicMemberLength
                "ops"
                (Compiler.CompilationModel.Expr.param "idx")
                1
            ])
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "count")
      ] := rfl

verity_contract DirectHelperCallStaticCompositeSmoke where
  storage
    sentinel : Uint256 := slot 0

  struct TokenPermissions where
    token : Address,
    amount : Uint256

  struct PermitTransferFrom where
    permitted : TokenPermissions,
    nonce : Uint256,
    deadline : Uint256

  function transferWithBalanceCheck
      (permit : PermitTransferFrom, depositor : Address, signature : Bytes,
       amount : Uint256, noteCommitment : Bytes32) : Uint256 := do
    let _depositorWord := addressToWord depositor
    let _noteCommitment := noteCommitment
    let sigSame := signature == signature
    if sigSame then
      return (add permit.permitted.amount amount)
    else
      return permit.nonce

  function allow_post_interaction_writes run
      (permit : PermitTransferFrom, depositor : Address, signature : Bytes,
       amount : Uint256, noteCommitment : Bytes32) : Uint256 := do
    let checked ← transferWithBalanceCheck permit depositor signature amount noteCommitment
    setStorage sentinel checked
    return checked

verity_contract DirectHelperCallUint256Bytes32AliasSmoke where
  storage
    sentinel : Uint256 := slot 0

  function rememberDigest (digest : Bytes32) : Unit := do
    setStorage sentinel digest

  function run (word : Uint256) : Unit := do
    rememberDigest word

verity_contract Uint8Smoke where
  storage
    sentinel : Uint256 := slot 0

  function acceptSig (sig : Tuple [Uint8, Bytes32, Bytes32]) : Unit := do
    let _sigValue := sig
    let v := sig_0
    let _r := sig_1
    let _s := sig_2
    setStorage sentinel v

  function sigV () : Uint8 := do
    return 27

verity_contract AddressHelpersSmoke where
  storage
    delegates : Address → Uint256 := slot 0
    ownersById : Uint256 → Uint256 := slot 1

  function setDelegate (owner : Address, delegate : Address) : Unit := do
    setMappingAddr delegates owner delegate

  function getDelegate (owner : Address) : Address := do
    let delegate ← getMappingAddr delegates owner
    return delegate

  function clearDelegate (owner : Address) : Unit := do
    setMappingAddr delegates owner zeroAddress

  function hasDelegate (owner : Address) : Bool := do
    let delegate ← getMappingAddr delegates owner
    return (delegate != zeroAddress)

  function isDelegateZero (owner : Address) : Bool := do
    let delegate ← getMappingAddr delegates owner
    return isZeroAddress delegate

  function setOwnerForId (tokenId : Uint256, owner : Address) : Unit := do
    require (owner != zeroAddress) "Invalid owner"
    setMappingUintAddr ownersById tokenId owner

  function getOwnerForId (tokenId : Uint256) : Address := do
    let owner ← getMappingUintAddr ownersById tokenId
    return owner

verity_contract ZeroAddressShadowSmoke where
  storage
    delegates : Address → Uint256 := slot 0

  function shadowWrite (zeroAddress : Address) : Unit := do
    setMappingAddr delegates zeroAddress zeroAddress

verity_contract ContextAccessorShadowSmoke where
  storage

  constants
    chainid : Uint256 := 31337

  immutables
    blockTimestamp : Uint256 := 12345
    msgSender : Address := (wordToAddress 42)

  function echoSenderName (msgSender : Address) : Address := do
    return msgSender

  function constantNamedChainid () : Uint256 := do
    return chainid

  function immutableNamedBlockTimestamp () : Uint256 := do
    return blockTimestamp

  function immutableNamedMsgSender () : Address := do
    return msgSender

end Contracts.Smoke
