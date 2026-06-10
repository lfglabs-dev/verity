import Contracts.Smoke.Intrinsics

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract UintMapSmoke where
  storage
    values : Uint256 → Uint256 := slot 0

  function setValue (key : Uint256, value : Uint256) : Unit := do
    setMappingUint values key value

  function getValue (key : Uint256) : Uint256 := do
    let current ← getMappingUint values key
    return current

verity_contract MappingChainSmoke where
  storage
    approvals : Address → Address → Address → Uint256 := slot 0

  function setApproval (owner : Address, spender : Address, delegate_ : Address, value : Uint256) : Unit := do
    setMappingN approvals [owner, spender, delegate_] value

  function getApproval (owner : Address, spender : Address, delegate_ : Address) : Uint256 := do
    let current ← getMappingN approvals [owner, spender, delegate_]
    return current

verity_contract MixedMappingChainSmoke where
  storage
    approvals : Address → Uint256 → Address → Uint256 := slot 0

  function setApproval (owner : Address, tokenId : Uint256, delegate_ : Address, value : Uint256) : Unit := do
    setMappingN approvals [addressToWord owner, tokenId, addressToWord delegate_] value

  function getApproval (owner : Address, tokenId : Uint256, delegate_ : Address) : Uint256 := do
    let current ← getMappingN approvals [addressToWord owner, tokenId, addressToWord delegate_]
    return current

verity_contract FixedArrayMappingStructSmoke where
  storage
    rows : MappingStruct(Uint256,[
      owner : Address @word 0,
      roots : FixedArray Bytes32 2 @word 1,
      proof : FixedArray (FixedArray Uint256 2) 2 @word 3
    ]) := slot 0

  function writeRoot1 (id : Uint256, root : Bytes32) : Unit := do
    setStructMember "rows" id "roots[1]" root

  function readRoot1 (id : Uint256) : Bytes32 := do
    let root ← structMember "rows" id "roots[1]"
    return root

  function writeProof11 (id : Uint256, value : Uint256) : Unit := do
    setStructMember "rows" id "proof[1][1]" value

  function readProof11 (id : Uint256) : Uint256 := do
    let value ← structMember "rows" id "proof[1][1]"
    return value

example :
    FixedArrayMappingStructSmoke.spec.fields.any (fun field =>
      field.name == "rows" &&
        match field.ty with
        | Compiler.CompilationModel.FieldType.mappingStruct
            Compiler.CompilationModel.MappingKeyType.uint256 members =>
            members.any (fun member => member.name == "roots[1]" && member.wordOffset == 2) &&
            members.any (fun member => member.name == "proof[1][1]" && member.wordOffset == 6)
        | _ => false) = true := by decide

verity_contract Bytes32Smoke where
  storage
    value : Uint256 := slot 0

  function setDigest (digest : Bytes32) : Unit := do
    setStorage value digest

  function getDigest () : Bytes32 := do
    let digest ← getStorage value
    return digest

verity_contract StorageArraySmoke where
  storage
    queue : Array Uint256 := slot 0

  function size () : Uint256 := do
    let size ← getStorageArrayLength queue
    return size

  function push (value : Uint256) : Unit := do
    pushStorageArray queue value

verity_contract StorageAddressArraySmoke where
  storage
    owners : Array Address := slot 0

  function size () : Uint256 := do
    let size ← getStorageArrayLength owners
    return size

  function firstOwner () : Address := do
    let owner ← getStorageArrayElement owners 0
    return owner

  function pushOwner (owner : Address) : Unit := do
    pushStorageArray owners owner

  function replaceFirstOwner (owner : Address) : Unit := do
    setStorageArrayElement owners 0 owner

verity_contract StorageBytes32ArraySmoke where
  storage
    digests : Array Bytes32 := slot 0

  function firstDigest () : Bytes32 := do
    let digest ← getStorageArrayElement digests 0
    return digest

  function pushDigest (digest : Bytes32) : Unit := do
    pushStorageArray digests digest

verity_contract StorageBoolArraySmoke where
  storage
    flags : Array Bool := slot 0

  function firstFlag () : Bool := do
    let flag ← getStorageArrayElement flags 0
    return flag

  function pushFlag (flag : Bool) : Unit := do
    pushStorageArray flags flag

  function setFirstFlag (flag : Bool) : Unit := do
    setStorageArrayElement flags 0 flag

def storageAddressArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageAddressArraySmoke.owners.slot then [11, 17] else [] }
  match StorageAddressArraySmoke.firstOwner seededState with
  | .success owner state =>
      owner == (11 : Address) &&
        state.storageArray StorageAddressArraySmoke.owners.slot == [11, 17]
  | .revert _ _ => false

example : storageAddressArrayExecutableReadsHead = true := by decide

def storageAddressArrayExecutablePushStoresWord : Bool :=
  match StorageAddressArraySmoke.pushOwner (19 : Address) Verity.defaultState with
  | .success () state =>
      state.storageArray StorageAddressArraySmoke.owners.slot == [19]
  | .revert _ _ => false

example : storageAddressArrayExecutablePushStoresWord = true := by decide

def storageAddressArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageAddressArraySmoke.owners.slot then [11, 17] else [] }
  match StorageAddressArraySmoke.replaceFirstOwner (29 : Address) seededState with
  | .success () state =>
      state.storageArray StorageAddressArraySmoke.owners.slot == [29, 17]
  | .revert _ _ => false

example : storageAddressArrayExecutableSetUpdatesHead = true := by decide

def storageBytes32ArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBytes32ArraySmoke.digests.slot then [41, 43] else [] }
  match StorageBytes32ArraySmoke.firstDigest seededState with
  | .success digest state =>
      digest == 41 &&
        state.storageArray StorageBytes32ArraySmoke.digests.slot == [41, 43]
  | .revert _ _ => false

example : storageBytes32ArrayExecutableReadsHead = true := by decide

def storageBoolArrayExecutableReadsHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBoolArraySmoke.flags.slot then [0, 1] else [] }
  match StorageBoolArraySmoke.firstFlag seededState with
  | .success flag state =>
      flag = false &&
        state.storageArray StorageBoolArraySmoke.flags.slot == [0, 1]
  | .revert _ _ => false

example : storageBoolArrayExecutableReadsHead = true := by decide

def storageBoolArrayExecutablePushStoresCanonicalWord : Bool :=
  match StorageBoolArraySmoke.pushFlag true Verity.defaultState with
  | .success () state =>
      state.storageArray StorageBoolArraySmoke.flags.slot == [1]
  | .revert _ _ => false

example : storageBoolArrayExecutablePushStoresCanonicalWord = true := by decide

def storageBoolArrayExecutableSetUpdatesHead : Bool :=
  let seededState : Verity.ContractState :=
    { Verity.defaultState with
      storageArray := fun idx =>
        if idx == StorageBoolArraySmoke.flags.slot then [0, 1] else [] }
  match StorageBoolArraySmoke.setFirstFlag true seededState with
  | .success () state =>
      state.storageArray StorageBoolArraySmoke.flags.slot == [1, 1]
  | .revert _ _ => false

example : storageBoolArrayExecutableSetUpdatesHead = true := by decide

/--
error: field 'queue' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement
-/
#guard_msgs in
verity_contract StorageArraySetStorageUnsupported where
  storage
    queue : Array Uint256 := slot 0

  function badWrite (value : Uint256) : Unit := do
    setStorage queue value

/--
error: field 'queue' is a storage dynamic array; use pushStorageArray/popStorageArray/setStorageArrayElement
-/
#guard_msgs in
verity_contract StorageArraySetStorageAddrUnsupported where
  storage
    queue : Array Uint256 := slot 0

  function badWrite (owner : Address) : Unit := do
    setStorageAddr queue owner

verity_contract MappingWordSmoke where
  storage
    words : Uint256 → Uint256 := slot 0

  function setWord1 (key : Uint256, value : Uint256) : Unit := do
    setMappingWord words key 1 value

  function getWord1 (key : Uint256) : Uint256 := do
    let word ← getMappingWord words key 1
    return word

  function isWord1NonZero (key : Uint256) : Bool := do
    let word ← getMappingWord words key 1
    return (word != 0)

verity_contract StorageWordsSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bytes32) : Array Uint256 := do
    returnStorageWords slots

verity_contract StorageWordsAddressSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Address) : Array Uint256 := do
    returnStorageWords slots

verity_contract StorageWordsBoolSmoke where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bool) : Array Uint256 := do
    returnStorageWords slots

/--
error: returnStorageWords requires an array with single-word static elements on the compilation-model path, got Verity.Macro.ValueType.array (Verity.Macro.ValueType.bytes)
-/
#guard_msgs in
verity_contract StorageWordsUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (slots : Array Bytes) : Array Uint256 := do
    returnStorageWords slots

/--
error: returnStorageWords currently requires a direct parameter reference on the compilation-model path
-/
#guard_msgs in
verity_contract StorageWordsConstructedUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function extSloadsLike (_ok : Bool, slots : Array Bytes32) : Array Uint256 := do
    returnStorageWords ([] : Array Bytes32)

/--
error: returnArray currently requires a direct parameter reference on the compilation-model path
-/
#guard_msgs in
verity_contract ReturnArrayConstructedUnsupported where
  storage
    sentinel : Uint256 := slot 0

  function echo (_ok : Bool, values : Array Uint256) : Array Uint256 := do
    returnArray ([] : Array Uint256)

end Contracts.Smoke
