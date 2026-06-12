import Contracts.Smoke.Declarations

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract TupleSmoke where
  storage
    values : Uint256 → Uint256 := slot 0
    authorized : Address → Uint256 := slot 1

  function setFromPair (pair : Tuple [Uint256, Uint256]) : Unit := do
    let _pairValue := pair
    let key := pair_0
    let value := pair_1
    setMappingUint values key value

  function getPair (key : Uint256) : Tuple [Uint256, Uint256] := do
    return (key, key)

  function processConfig (cfg : Tuple [Address, Address, Uint256]) : Unit := do
    let _cfgValue := cfg
    let owner := cfg_0
    let _delegate := cfg_1
    let flag := cfg_2
    setMapping authorized owner flag

verity_contract NamedStructParamSmoke where
  storage
    values : Uint256 → Uint256 := slot 0

  struct FeeConfig where
    borrowTakerFeeRatio : Uint256,
    lendMakerFeeRatio : Uint256

  struct OrderConfig where
    feeConfig : FeeConfig,
    maker : Address

  function readBorrowFee (feeConfig : FeeConfig) : Uint256 := do
    return feeConfig.borrowTakerFeeRatio

  function storeNestedFee (config : OrderConfig, key : Uint256) : Unit := do
    setMappingUint values key config.feeConfig.borrowTakerFeeRatio

  function readNestedMaker (config : OrderConfig) : Address := do
    return config.maker

verity_contract NestedStructStorageSmoke where
  storage
    state : StorageStruct [
      merkleRoot : Uint256 @word 0,
      merkleTree : StorageStruct [
        maxIndex : Uint256 @word 0 packed(0,40),
        numberOfLeaves : Uint256 @word 0 packed(40,40),
        elements : Uint256 → Uint256 @word 1
      ] @word 1,
      verifierRouter : Address @word 4
    ] := slot 0

  function readLeaves () : Uint256 := do
    let n ← getStorage state.merkleTree.numberOfLeaves
    return n

  function writeLeaves (n : Uint256) : Unit := do
    setStorage state.merkleTree.numberOfLeaves n

  function writeElement (key : Uint256, value : Uint256) : Unit := do
    setMappingWord state.merkleTree.elements key 0 value

  function readRouter () : Address := do
    let router ← getStorageAddr state.verifierRouter
    return router

example : NestedStructStorageSmoke.state.merkleTree.numberOfLeaves.slot = 1 := by decide
example : NestedStructStorageSmoke.state.merkleTree.elements.slot = 2 := by decide
example : NestedStructStorageSmoke.state.verifierRouter.slot = 4 := by decide

/--
error: unknown variable 'feeConfig.borrowTakerFeeRatio'
-/
#guard_msgs in
verity_contract NamedStructNonLeafProjectionRejected where
  storage

  struct FeeConfig where
    borrowTakerFeeRatio : Uint256,
    lendMakerFeeRatio : Uint256

  struct OrderConfig where
    feeConfig : FeeConfig,
    maker : Address

  function bad (config : OrderConfig) : Uint256 := do
    let feeConfig := config.feeConfig
    return feeConfig.borrowTakerFeeRatio

/--
error: unknown variable 'pair_0'
-/
#guard_msgs in
verity_contract NamedStructTupleProjectionRejected where
  storage

  struct TupleConfig where
    pair : Tuple [Uint256, Uint256],
    maker : Address

  function badTuple (config : TupleConfig) : Uint256 := do
    let pair := config.pair
    return pair_0

/--
error: local binding 'notes' currently cannot bind dynamic values (Verity.Macro.ValueType.array (Verity.Macro.ValueType.uint256)) to local variables on the compilation-model path; use the parameter directly
-/
#guard_msgs in
verity_contract NamedStructDynamicProjectionRejected where
  storage

  struct DynamicConfig where
    notes : Array Uint256,
    maker : Address

  function badDynamic (config : DynamicConfig) : Uint256 := do
    let notes := config.notes
    return 0

-- Dynamic-root leaf projection (verity#1832): a single-word static field
-- on a struct parameter whose ABI encoding is dynamic (carries nested
-- dynamic members) is now supported. Lowers to `Expr.paramDynamicHeadWord`.
verity_contract NamedStructDynamicRootLeafProjection where
  storage

  struct DynamicConfig where
    notes : Array Uint256,
    maker : Address

  function goodDynamicLeaf (config : DynamicConfig) : Address := do
    return config.maker

verity_contract NamedStructReturnSmoke where
  storage

  struct FeeConfig where
    borrowTakerFeeRatio : Uint256,
    lendMakerFeeRatio : Uint256

  function goodReturn (borrowFee : Uint256, lendFee : Uint256) : FeeConfig := do
    return FeeConfig.mk borrowFee lendFee

verity_contract CurveCutArraySmoke where
  storage
    lastXt : Uint256 := slot 0
    lastLiq : Uint256 := slot 1
    lastOffset : Uint256 := slot 2

  function firstCutXt (cuts : Array (Tuple [Uint256, Uint256, Int256])) : Uint256 := do
    let (xtReserve, _liqSquare, _offset) := arrayElement cuts 0
    return xtReserve

  function returnCut (cuts : Array (Tuple [Uint256, Uint256, Int256]), idx : Uint256) : Tuple [Uint256, Uint256, Int256] := do
    return arrayElement cuts idx

  function storeCut (cuts : Array (Tuple [Uint256, Uint256, Int256]), idx : Uint256) : Unit := do
    let (xtReserve, liqSquare, offset) := arrayElement cuts idx
    setStorage lastXt xtReserve
    setStorage lastLiq liqSquare
    setStorage lastOffset (toUint256 offset)

  function storeTwoCuts (cuts : Array (Tuple [Uint256, Uint256, Int256]), firstIdx : Uint256, secondIdx : Uint256) : Unit := do
    let (firstXt, _firstLiq, _firstOffset) := arrayElement cuts firstIdx
    let (secondXt, _secondLiq, _secondOffset) := arrayElement cuts secondIdx
    setStorage lastXt firstXt
    setStorage lastLiq secondXt

/--
error: arrayElement currently supports only arrays with single-word static elements on the compilation-model path, got Verity.Macro.ValueType.array
  (Verity.Macro.ValueType.tuple [Verity.Macro.ValueType.uint256, Verity.Macro.ValueType.uint256])
-/
#guard_msgs in
verity_contract CurveCutPlainTupleArrayElementRejected where
  storage

  function badPlainRead (cuts : Array (Tuple [Uint256, Uint256])) : Uint256 := do
    let cut := arrayElement cuts 0
    return 0

def curveCutArrayExecutableReadsTupleElement : Bool :=
  match CurveCutArraySmoke.firstCutXt #[(11, 13, toInt256 17)] Verity.defaultState with
  | .success value _ => value == 11
  | _ => false

example : curveCutArrayExecutableReadsTupleElement = true := by decide

verity_contract DynamicStructArraySmoke where
  storage
    lastToken : Address := slot 0
    lastAmount : Uint256 := slot 1

  struct Note where
    owner : Address,
    amount : Uint256,
    nullifier : Bytes32

  struct Ciphertext where
    data : Array Uint256,
    nonce : Bytes32

  struct Transaction where
    proof : Array Uint256,
    note : Note,
    ciphertexts : Array Ciphertext,
    token : Address,
    fee : Uint256

  struct WrappedCiphertext where
    ciphertext : Ciphertext,
    token : Address,
    fee : Uint256

  function tokenOf (txs : Array Transaction, idx : Uint256) : Address := do
    return (arrayElement txs idx).token

  function feeOf (txs : Array Transaction, idx : Uint256) : Uint256 := do
    return (arrayElement txs idx).fee

  function wrappedTokenOf (items : Array WrappedCiphertext, idx : Uint256) : Address := do
    return (arrayElement items idx).token

  function storeTokenAndFee (txs : Array Transaction, idx : Uint256) : Unit := do
    setStorageAddr lastToken (arrayElement txs idx).token
    setStorage lastAmount (arrayElement txs idx).fee

def dynamicStructArrayExecutableReadsStaticLeaves : Bool :=
  let note : DynamicStructArraySmoke.Note := {
    owner := 0x1234,
    amount := 99,
    nullifier := 7
  }
  let tx : DynamicStructArraySmoke.Transaction := {
    proof := #[1, 2, 3],
    note := note,
    ciphertexts := #[],
    token := 0xabcd,
    fee := 5
  }
  match DynamicStructArraySmoke.feeOf #[tx] 0 Verity.defaultState with
  | .success value _ => value == 5
  | _ => false

example : dynamicStructArrayExecutableReadsStaticLeaves = true := by decide

verity_contract PackedStorageWriteSmoke where
  storage
    stateRoot : Uint256 := slot 0

  function writeSlot0 (isClosed : Bool, maxTotalSupply : Uint256) : Unit := do
    let closedWord := boolToWord isClosed
    let slot0 := bitOr closedWord (shl 8 maxTotalSupply)
    setPackedStorage stateRoot 0 slot0

  function writeSlot1 (accruedProtocolFees : Uint256, normalizedUnclaimedWithdrawals : Uint256) : Unit := do
    let slot1 := bitOr accruedProtocolFees (shl 128 normalizedUnclaimedWithdrawals)
    setPackedStorage stateRoot 1 slot1

def packedStorageExecutableWritesExplicitWordOffset : Bool :=
  match PackedStorageWriteSmoke.writeSlot1 7 9 Verity.defaultState with
  | .success _ state =>
      state.storage 0 == 0 &&
      state.storage 1 == bitOr 7 (shl 128 9)
  | _ => false

example : packedStorageExecutableWritesExplicitWordOffset = true := by decide

verity_contract PackedAddressStorageWriteSmoke where
  storage
    owner : Address := slot 0

  function writeOwnerWord (word : Uint256) : Address := do
    setPackedStorage owner 0 word
    let current ← getStorageAddr owner
    return current

def packedStorageExecutableUpdatesAddressMirror : Bool :=
  match PackedAddressStorageWriteSmoke.writeOwnerWord 0xA11CE Verity.defaultState with
  | .success value state =>
      value == Verity.wordToAddress 0xA11CE &&
      state.storage 0 == 0xA11CE &&
      state.storageAddr 0 == Verity.wordToAddress 0xA11CE
  | _ => false

example : packedStorageExecutableUpdatesAddressMirror = true := by decide

end Contracts.Smoke
