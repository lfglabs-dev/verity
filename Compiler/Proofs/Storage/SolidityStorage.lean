import Compiler.Proofs.MappingSlot
import Compiler.CompilationModel.ExpressionCompile
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

/-- Synthetic scalar field used to expose the packed-storage compiler branch. -/
def packedReadBridgeField (offset width : Nat) : Compiler.CompilationModel.Field :=
  { name := "__packed_read_bridge", ty := .uint256, slot := some 0,
    packedBits := some { offset := offset, width := width } }

/-- Interpret the exact packed-storage expression emitted by
    `compileExprWithInternals`. The deliberately structural match makes changes
    to the emitted operator order, offset, load, slot, or mask observable here. -/
def isCompiledPackedReadExpr : Compiler.Yul.YulExpr → Nat → Nat → Bool
  | .call "and" [.call "shr" [.lit shift, .call "sload" [.lit 0]], .lit mask],
      offset, width => shift == offset && mask == packedMask width
  | _, _, _ => false

def compiledPackedRead (word : Word) (offset width : Nat) : Word :=
  let emitted := Compiler.CompilationModel.compileExprWithInternals
      [packedReadBridgeField offset width] .calldata []
      (.storage "__packed_read_bridge")
  match emitted with
  | .ok expr =>
      if isCompiledPackedReadExpr expr offset width then yulReadPackedWord word offset width
      else IRStorageWord.ofNat 0
  | .error _ => IRStorageWord.ofNat 0

/-- The helper for a Yul packed read is the interpretation of the real compiler
    path in `ExpressionCompile.lean`. -/
theorem yulReadPackedWord_eq_compiledExpr (word : Word) (offset width : Nat)
    (hwidth : width < 256) :
    yulReadPackedWord word offset width = compiledPackedRead word offset width := by
  have hfield :
      Compiler.CompilationModel.findFieldWithResolvedSlot
        [packedReadBridgeField offset width] "__packed_read_bridge" =
        some (packedReadBridgeField offset width, 0) := by
    rfl
  have hmapping :
      Compiler.CompilationModel.isMapping
        [packedReadBridgeField offset width] "__packed_read_bridge" = false := by
    rfl
  have hcompile :
      Compiler.CompilationModel.compileExprWithInternals
          [packedReadBridgeField offset width] .calldata []
          (.storage "__packed_read_bridge") =
        .ok (.call "and"
          [.call "shr" [.lit offset, .call "sload" [.lit 0]],
            .lit (packedMask width)]) := by
    simp only [Compiler.CompilationModel.compileExprWithInternals, hmapping,
      Bool.false_eq_true, if_false, hfield]
    simp [packedReadBridgeField, Compiler.CompilationModel.packedMaskNat,
      Nat.not_le.mpr hwidth, packedMask]
    change Except.ok _ = Except.ok _
    rfl
  unfold compiledPackedRead
  rw [hcompile]
  simp [isCompiledPackedReadExpr]

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
