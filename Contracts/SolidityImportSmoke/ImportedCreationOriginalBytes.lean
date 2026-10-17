import Contracts.SolidityImportSmoke.ImportedCreationOriginalExecution

namespace Contracts.SolidityImportSmoke.ImportedCreationOriginalBytes
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationDecodedPrefix

theorem field0 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 0 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 0))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  rw [ImportedCreationDecodedMarket.prefix_first_byte _ _ (by omega) (by have := lane.isLt; omega)]
  have field := ImportedCreationDecoderFields.first_bytes
    (ImportedCreationDecoderHead.completed state) (rootPointer state) 128 lane
  exact field

theorem field32 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 32 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 32))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  rw [ImportedCreationDecodedMarket.prefix_first_byte _ _ (by omega) (by have := lane.isLt; omega)]
  have field := ImportedCreationDecoderFields.middle_bytes
    (ImportedCreationDecoderHead.completed state) (rootPointer state) 128 lane
  exact field

theorem field64 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 64 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 64))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  rw [ImportedCreationDecodedMarket.prefix_first_byte _ _ (by omega) (by have := lane.isLt; omega)]
  have field := ImportedCreationDecoderFields.last_bytes
    (ImportedCreationDecoderHead.completed state) (rootPointer state) 128 lane
  exact field

theorem field128 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 128 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 128))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  unfold ImportedCreationDecodedMarket.prefixCompleted
  rw [ImportedCreationDecodedMarket.bytes128, ImportedCreationDecodedMarket.original_word]

theorem field160 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 160 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 160))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  unfold ImportedCreationDecodedMarket.prefixCompleted
  rw [ImportedCreationDecodedMarket.bytes160, ImportedCreationDecodedMarket.original_word]

theorem field192 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 192 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 192))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  unfold ImportedCreationDecodedMarket.prefixCompleted
  rw [ImportedCreationDecodedMarket.bytes192, ImportedCreationDecodedMarket.original_word]

theorem field224 (oracle : DenoteOracle) (state : DenoteState) (lane : Fin 32) :
    (completed oracle state).world.physicalByte (128 + 224 + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat (ImportedCalldataWord.word state (rootPointer state + 224))) lane := by
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  unfold ImportedCreationDecodedMarket.prefixCompleted
  rw [ImportedCreationDecodedMarket.bytes224, ImportedCreationDecodedMarket.original_word]

theorem element (oracle : DenoteOracle) (state : DenoteState) (index offset : Nat)
    (lane : Fin 32) (live : index < count state)
    (valid : offset = 0 ∨ offset = 32 ∨ offset = 64 ∨ offset = 96) :
    (completed oracle state).world.physicalByte (free state + index * 128 + offset + lane.val) =
      valueWord (Verity.Core.Uint256.ofNat
        (ImportedCalldataWord.word state (data state + index * 128 + offset))) lane := by
  have geometry : free state = 384 + 32 * (count state + 1) := rfl
  change (ImportedCreationDecodedMarket.prefixCompleted state).world.physicalByte _ = _
  rw [ImportedCreationDecodedMarket.prefix_array_byte _ _ (by rw [geometry]; omega)]
  exact ImportedCreationDecodedArray.element_byte state index offset lane live valid

end Contracts.SolidityImportSmoke.ImportedCreationOriginalBytes
