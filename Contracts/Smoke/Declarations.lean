import Contracts.Smoke.Arithmetic

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract StatelessSmoke where
  storage

  function echoWord (value : Uint256) : Uint256 := do
    return value

  function whoAmI () : Address := do
    let sender ← msgSender
    return sender

verity_contract MutabilitySmoke where
  storage
    owner : Address := slot 0

  constructor (initialOwner : Address) := do
    setStorageAddr owner initialOwner

  function payable deposit () : Uint256 := do
    let value ← msgValue
    return value

  function view currentOwner () : Address := do
    let ownerAddr ← getStorageAddr owner
    return ownerAddr

  function pure double (value : Uint256) : Uint256 := do
    return (add value value)

verity_contract SpecialEntrypointSmoke where
  storage
    receiveCount : Uint256 := slot 0
    fallbackCount : Uint256 := slot 1

  receive := do
    let current ← getStorage receiveCount
    setStorage receiveCount (add current 1)

  fallback := do
    let current ← getStorage fallbackCount
    setStorage fallbackCount (add current 1)

  function getReceiveCount () : Uint256 := do
    let current ← getStorage receiveCount
    return current

  function getFallbackCount () : Uint256 := do
    let current ← getStorage fallbackCount
    return current

verity_contract ConstantSmoke where
  storage

  constants
    basisPoints : Uint256 := 10000
    mintFeeBps : Uint256 := 30
    treasury : Address := (wordToAddress 42)

  function feeOn (amount : Uint256) : Uint256 := do
    let fee := div (mul amount mintFeeBps) basisPoints
    return fee

  function treasuryAddr () : Address := do
    return treasury

verity_contract ImmutableSmoke where
  storage
    owner : Address := slot 0

  constants
    offset : Uint256 := 2

  immutables
    seededSupply : Uint256 := (add seed offset)
    treasury : Address := ownerSeed

  constructor (seed : Uint256, ownerSeed : Address) := do
    setStorageAddr owner ownerSeed

  function supplyCap () : Uint256 := do
    return seededSupply

  function treasuryAddr () : Address := do
    return treasury

  function shadowed (seededSupply : Uint256) : Uint256 := do
    return seededSupply

verity_contract TypedImmutableSmoke where
  storage

  immutables
    paused : Bool := true
    feeBps : Uint8 := 7
    domainTag : Bytes32 := 42

  function isPaused () : Bool := do
    return paused

  function feeScale () : Uint8 := do
    return feeBps

  function domainSeparator () : Bytes32 := do
    return domainTag

verity_contract InitializerSmoke where
  storage
    initializedVersion : Uint256 := slot 0
    owner : Address := slot 1
    paused : Uint256 := slot 2

  function initOwner (seedOwner : Address) initializer(initializedVersion) : Unit := do
    setStorageAddr owner seedOwner

  function upgradeToV2 () reinitializer(initializedVersion, 2) : Unit := do
    setStorage paused 1

/--
error: initializer guard field 'owner' must be a Uint256 storage slot
-/
#guard_msgs in
verity_contract InitializerGuardFieldTypeRejected where
  storage
    owner : Address := slot 0

  function initOwner () initializer(owner) : Unit := do
    pure ()

/--
error: reinitializer version must be greater than 0
-/
#guard_msgs in
verity_contract InitializerZeroVersionRejected where
  storage
    initializedVersion : Uint256 := slot 0

  function upgradeToV0 () reinitializer(initializedVersion, 0) : Unit := do
    pure ()

/--
error: contract constants must be compile-time expressions; 'blobbasefee' is runtime-dependent
-/
#guard_msgs in
verity_contract ConstantRuntimeBuiltinRejected where
  storage

  constants
    seededAt : Uint256 := blobbasefee

  function seeded () : Uint256 := do
    return seededAt

/--
 error: contract immutables currently support only Uint256, Int256, Uint8, Address, Bytes32, and Bool; 'metadata' uses unsupported type
-/
#guard_msgs in
verity_contract ImmutableTypeRejected where
  storage

  immutables
    metadata : String := "paused"

  function metadataWord () : Uint256 := do
    return 0

/--
error: immutable 'fee' expects Verity.Macro.ValueType.uint256, got Verity.Macro.ValueType.bool
-/
#guard_msgs in
verity_contract ImmutableBoolAssignedToWordRejected where
  storage

  immutables
    fee : Uint256 := true

  function feeWord () : Uint256 := do
    return fee

/--
error: immutable 'owner' expects Verity.Macro.ValueType.address, got Verity.Macro.ValueType.bool
-/
#guard_msgs in
verity_contract ImmutableBoolAssignedToAddressRejected where
  storage

  immutables
    owner : Address := true

  function ownerAddr () : Address := do
    return owner

/--
error: immutable 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract ImmutableStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  immutables
    owner : Address := zeroAddress

  function getOwner () : Address := do
    return owner

/--
error: immutable 'basisPoints' conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ImmutableConstantNameConflictRejected where
  storage

  constants
    basisPoints : Uint256 := 10000

  immutables
    basisPoints : Uint256 := 9999

  function getBasisPoints () : Uint256 := do
    return basisPoints

/--
error: duplicate immutable declaration 'seededSupply'
-/
#guard_msgs in
verity_contract DuplicateImmutableRejected where
  storage

  immutables
    seededSupply : Uint256 := 1
    seededSupply : Uint256 := 2

  function getSeededSupply () : Uint256 := do
    return seededSupply

/--
error: duplicate storage field declaration 'owner'
-/
#guard_msgs in
verity_contract DuplicateStorageFieldRejected where
  storage
    owner : Address := slot 0
    owner : Address := slot 1

  function getOwner () : Address := do
    return zeroAddress

/--
error: constant 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract ConstantStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  constants
    owner : Uint256 := 1

  function ownerWord () : Uint256 := do
    return owner

/--
error: duplicate constant declaration 'basisPoints'
-/
#guard_msgs in
verity_contract DuplicateConstantRejected where
  storage

  constants
    basisPoints : Uint256 := 10000
    basisPoints : Uint256 := 9999

  function getBasisPoints () : Uint256 := do
    return basisPoints

/--
error: function 'owner' conflicts with a storage field of the same name
-/
#guard_msgs in
verity_contract FunctionStorageNameConflictRejected where
  storage
    owner : Address := slot 0

  function owner () : Address := do
    return zeroAddress

/--
error: function 'fee' conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract FunctionConstantNameConflictRejected where
  storage

  constants
    fee : Uint256 := 7

  function fee () : Uint256 := do
    return 0

/--
error: duplicate function declaration 'echo()'
-/
#guard_msgs in
verity_contract DuplicateFunctionRejected where
  storage

  function echo () : Uint256 := do
    return 1

  function echo () : Uint256 := do
    return 2

verity_contract FunctionOverloadSmoke where
  storage

  function echo (a : Uint256) : Uint256 := do
    return a

  function echo (a : Address) : Uint256 := do
    return (addressToWord a)

  function echo (a : Uint256, b : Uint256) : Uint256 := do
    return (add a b)

-- #1747: higher-order internal helpers (function-pointer parameters) are now
-- supported via a compile-time monomorphization pre-pass. `apply` takes a
-- function pointer and is specialized at each call site that passes a
-- statically-known helper, so the contract lowers to first-order helpers only.
verity_contract FunctionPointerParamSmoke where
  storage

  function inc (x : Uint256) : Uint256 := do
    return (add x 1)

  function apply (f : Uint256 → Uint256, x : Uint256) : Uint256 := do
    let y ← f x
    return y

  function runInc (n : Uint256) : Uint256 := do
    let r ← apply inc n
    return r

-- The remaining genuine restriction (#1747): a function-pointer argument must be
-- a statically-known internal helper name, not a runtime value or expression.
/--
error: #1747: function-pointer argument 'n' is not a known internal helper in this contract
-/
#guard_msgs in
verity_contract FunctionPointerDynamicArgRejected where
  storage

  function apply (f : Uint256 → Uint256, x : Uint256) : Uint256 := do
    let y ← f x
    return y

  function bad (n : Uint256) : Uint256 := do
    let r ← apply n n
    return r

/--
error: duplicate function ABI signature 'echo(scalar_uint256)' after ABI erasure
-/
#guard_msgs in
verity_contract NewtypeErasedOverloadRejected where
  types
    Amount : Uint256
    Shares : Uint256
  storage

  function echo (a : Amount) : Uint256 := do
    return a

  function echo (a : Shares) : Uint256 := do
    return a

/--
error: duplicate function ABI signature 'echo(tuple2_scalar_uint8__scalar_uint256)' after ABI erasure
-/
#guard_msgs in
verity_contract AdtErasedOverloadRejected where
  inductive
    LeftBox := | LeftValue(value : Uint256)
    RightBox := | RightValue(value : Uint256)
  storage

  function echo (a : LeftBox) : Uint256 := do
    return 0

  function echo (a : RightBox) : Uint256 := do
    return 0

verity_contract HelperExternalArgumentSmoke where
  storage
    saved : Uint256 := slot 0

  linked_externals
    external echo(Uint256) -> (Uint256)

  function idWord (a : Uint256) : Uint256 := do
    return a

  function pair (a : Uint256) : Tuple [Uint256, Uint256] := do
    return (a, add a 1)

  function put (a : Uint256) : Unit := do
    setStorage saved a

  function reentrancy_trusted bindExternalArg (x : Uint256) : Uint256 := do
    let y ← idWord (externalCall "echo" [x])
    return y

  function reentrancy_trusted tupleExternalArg (x : Uint256) : Uint256 := do
    let (a, b) ← pair (externalCall "echo" [x])
    return (add a b)

  function reentrancy_trusted statementExternalArg (x : Uint256) : Unit := do
    put (externalCall "echo" [x])

verity_contract BlockTimestampSmoke where
  storage

  function nowish () : Uint256 := do
    let t ← Verity.blockTimestamp
    return t

  function timestampPlus (delta : Uint256) : Uint256 := do
    let t ← blockTimestamp
    return (add t delta)

  function blobFeePlus (delta : Uint256) : Uint256 := do
    let fee ← blobbasefee
    return (add fee delta)

example :
    (BlockTimestampSmoke.nowish.run { Verity.defaultState with blockTimestamp := 123 }).getValue? =
      some 123 := by
  decide

example :
    (BlockTimestampSmoke.timestampPlus 7 |>.run { Verity.defaultState with blockTimestamp := 123 }).getValue? =
      some 130 := by
  decide

example :
    (BlockTimestampSmoke.blobFeePlus 7 |>.run { Verity.defaultState with blobBaseFee := 123 }).getValue? =
      some 130 := by
  decide

/--
error: context accessor 'blockTimestamp' is monadic; use `let x ← blockTimestamp` before using it in a pure expression
-/
#guard_msgs in
verity_contract PureBlockTimestampAccessorRejected where
  storage

  function nowish () : Uint256 := do
    let t := blockTimestamp
    return t

/--
error: storage field 'spec' conflicts with reserved generated declaration 'spec'
-/
#guard_msgs in
verity_contract ReservedSpecStorageNameRejected where
  storage
    spec : Address := slot 0

  function owner () : Address := do
    return zeroAddress

/--
error: function 'settle_model' conflicts with reserved generated declaration 'settle_model'
-/
#guard_msgs in
verity_contract FunctionGeneratedHelperNameRejected where
  storage

  function settle () : Uint256 := do
    return 1

  function settle_model () : Uint256 := do
    return 2

/--
error: function 'price' generates helper 'price_model' that conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ConstantFunctionHelperCollisionRejected where
  storage

  constants
    price_model : Uint256 := 7

  function price () : Uint256 := do
    return 3

/--
error: function 'structMember' conflicts with reserved generated declaration 'structMember'
-/
#guard_msgs in
verity_contract StructMappingGeneratedReadHelperCollisionRejected where
  storage
    positions : MappingStruct(Address,[delegate @word 0]) := slot 0

  function structMember () : Uint256 := do
    return 1

/--
error: immutable 'setStructMember2' conflicts with reserved generated declaration 'setStructMember2'
-/
#guard_msgs in
verity_contract StructMappingGeneratedWriteHelperImmutableCollisionRejected where
  storage
    approvals : MappingStruct2(Address,Address,[allowance @word 0]) := slot 0

  immutables
    setStructMember2 : Uint256 := 1

  constructor () := do
    pure ()

  function allowanceOf (owner : Address, spender : Address) : Uint256 := do
    let amount ← structMember2 "approvals" owner spender "allowance"
    return amount

/--
error: function 'quote' generates internal declaration 'quote__14xscalar_uint256' that conflicts with a contract constant of the same name
-/
#guard_msgs in
verity_contract ConstantOverloadGeneratedNameCollisionRejected where
  storage

  constants
    quote__14xscalar_uint256 : Uint256 := 7

  function quote (amount : Uint256) : Uint256 := do
    return amount

  function quote (recipient : Address) : Uint256 := do
    return (addressToWord recipient)

/--
error: function 'quote' generates internal declaration 'quote__14xscalar_uint256' that conflicts with an immutable of the same name
-/
#guard_msgs in
verity_contract ImmutableOverloadGeneratedNameCollisionRejected where
  storage

  immutables
    quote__14xscalar_uint256 : Uint256 := 7

  function quote (amount : Uint256) : Uint256 := do
    return amount

  function quote (recipient : Address) : Uint256 := do
    return (addressToWord recipient)

#guard_msgs in
verity_contract OverloadSignatureEncodingSmoke where
  types
    tuple_uint256 : Uint256
  storage

  function quote (amount : tuple_uint256) : Uint256 := do
    return amount

  function quote (pair : Tuple [Uint256, Uint256]) : Uint256 := do
    let _pairValue := pair
    return pair_0

end Contracts.Smoke
