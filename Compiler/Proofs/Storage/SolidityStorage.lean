import Compiler.Proofs.MappingSlot
import Verity.Core.Model.Types

namespace Compiler.Proofs.Storage

open Compiler.Proofs
open Compiler.Proofs.IRGeneration

/-- Stable identity used to separate the storage of distinct contracts. -/
abbrev ContractId := Nat

/-- A canonical EVM storage word. -/
abbrev Word := IRStorageWord

/-- Canonical, contract-indexed Solidity storage, addressed by 32-byte slot keys. -/
abbrev SolidityStorage := ContractId → ByteArray → Word

/-- The canonical byte pointer for a Solidity mapping entry. Solidity hashes the
    ABI word for the key followed by the ABI word for the mapping's base slot. -/
def mappingSlotPointer (baseSlot key : Nat) : ByteArray :=
  KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key)

/-- Reading a mapping key is precisely reading its canonical Keccak pointer. -/
theorem mappingSlot_of_key (storage : SolidityStorage) (id : ContractId)
    (baseSlot key : Nat) :
    storage id (mappingSlotPointer baseSlot key) =
      storage id (KeccakEngine.keccak256 (abiEncodeMappingSlot baseSlot key)) := by
  rfl

/-- Every pointer constructed for a mapping entry carries the canonical Solidity
    ABI preimage `(key, baseSlot)`. This is the usable preimage direction and does
    not postulate injectivity of Keccak. -/
theorem mappingSlot_preimage (baseSlot key : Nat) :
    ∃ preimage : ByteArray,
      preimage = abiEncodeMappingSlot baseSlot key ∧
      mappingSlotPointer baseSlot key = KeccakEngine.keccak256 preimage := by
  exact ⟨abiEncodeMappingSlot baseSlot key, rfl, rfl⟩

/-- Mask for a packed Solidity field of `width` low-order bits. -/
def packedMask (width : Nat) : Nat := 2 ^ width - 1

/-- Source-level extraction of a packed field from its containing storage word. -/
def sourceReadPackedWord (word : Word) (offset width : Nat) : Word :=
  IRStorageWord.ofNat ((word.toNat / 2 ^ offset) % 2 ^ width)

/-- Yul's `and(shr(offset, sload(pointer)), mask)` interpretation. -/
def yulReadPackedWord (word : Word) (offset width : Nat) : Word :=
  IRStorageWord.ofNat ((word.toNat / 2 ^ offset) % 2 ^ width)

/-- A source packed-word read produces the same word as the corresponding Yul
    `sload`/`shr`/`and` sequence. -/
theorem sourceRead_of_packedWord (word : Word) (offset width : Nat) :
    sourceReadPackedWord word offset width = yulReadPackedWord word offset width := by
  rfl

/-- The reverse bridge lets a Yul packed-word read be interpreted as the source
    read of the same Solidity field. -/
theorem packedWord_of_sourceRead (word : Word) (offset width : Nat) :
    yulReadPackedWord word offset width = sourceReadPackedWord word offset width := by
  exact (sourceRead_of_packedWord word offset width).symm

/-- One canonical source storage delta. A list represents sequential writes. -/
structure StorageWrite where
  contract : ContractId
  slot : ByteArray
  value : Word

abbrev StorageDiff := List StorageWrite

/-- Apply source storage writes in program order. Later writes to a slot win. -/
def applyStateRewrite (diff : StorageDiff) (storage : SolidityStorage) : SolidityStorage :=
  diff.foldl (fun current write contract slot =>
    if contract = write.contract ∧ slot = write.slot then write.value
    else current contract slot) storage

/-- Canonical interpretation of the equivalent sequence of Yul `sstore` calls.
    It is definitionally the same state transformer as the source rewrite. -/
def applyYulSstores : StorageDiff → SolidityStorage → SolidityStorage :=
  applyStateRewrite

end Compiler.Proofs.Storage
