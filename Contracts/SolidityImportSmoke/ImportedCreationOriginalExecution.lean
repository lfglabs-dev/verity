import Contracts.SolidityImportSmoke.ImportedCreationEncoderEntry

namespace Contracts.SolidityImportSmoke.ImportedCreationOriginalExecution
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationDecodedPrefix ImportedCreationEncoderEntry

def segment := prefixSegment ++ ImportedCreationEncodedPacking.segment

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 88) = some segment := by rfl

/-- Actual original-transaction execution through all decoder, write and packing nodes. -/
theorem execute (oracle : DenoteOracle) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (rootOffsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : rootPointer state + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit)
    (canonical32 : ImportedCalldataWord.word state (rootPointer state + 32) < 2^160)
    (canonical64 : ImportedCalldataWord.word state (rootPointer state + 64) < 2^160)
    (offsetBound : ImportedCreationDecoderArrayHead.relative state (rootPointer state) ≤ 2^64 - 1)
    (arrayAvailable : header state + 32 ≤ state.world.calldataSize.val)
    (payloadAvailable : data state + count state * 128 ≤ state.world.calldataSize.val)
    (canonical : ∀ i < count state, ImportedCalldataWord.word state (data state + i * 128) < 2^160 ∧
      ImportedCalldataWord.word state (data state + i * 128 + 96) < 2^160)
    (canonical192 : ImportedCalldataWord.word state (rootPointer state + 192) < 2^160)
    (canonical224 : ImportedCalldataWord.word state (rootPointer state + 224) < 2^160)
    (budget : head state + (320 + 128 * count state) + 32 +
      32 * ((11 + (320 + 128 * count state) + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle actualFields state segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world
        (head state + (320 + 128 * count state) + 32) (11 + (320 + 128 * count state)) =
        ImportedCreationHeaderAllocation.prefixBytes ++
          ImportedCreationAbiLayout.abiBytes (completed oracle state) 128 := by
  have allocation : free state + count state * 128 ≤ 2^64 - 1 := by
    change head state ≤ 2^64 - 1
    omega
  have decoded := execute_prefix oracle state headAvailable rootOffsetBound tupleAvailable sizeBound
    canonical32 canonical64 offsetBound arrayAvailable allocation payloadAvailable canonical canonical192 canonical224
  obtain ⟨final, encoded, bytes⟩ := execute_encoder oracle state budget
  refine ⟨final, ?_, bytes⟩
  rw [segment, SolidityImport.exec_append, decoded]
  exact encoded

end Contracts.SolidityImportSmoke.ImportedCreationOriginalExecution
