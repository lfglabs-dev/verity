import Compiler.Proofs.IRGeneration.ImportedAbiTupleHead
import Contracts.SolidityImportSmoke.ImportedCreationDecoderAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationDecoderHead
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration

abbrev rootSegment := SolidityImport.AbiLowering.tupleHead "_verity_slice_tmp_0_calldata" 3 0 8
abbrev rootState (state : DenoteState) := ImportedAbiTupleHead.decoded
  (ImportedCreationDecoderAllocation.initialized state) "_verity_slice_tmp_0_calldata" 0

def segment : List Stmt := [.mstore (.literal 64) (.literal 128)] ++
  rootSegment ++ ImportedCreationDecoderAllocation.segment

def completed (state : DenoteState) : DenoteState :=
  ImportedCreationDecoderAllocation.allocated (rootState state) 128

theorem actual_root :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 1).take 4) = some rootSegment := by rfl

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body.take 10) = some segment := by rfl

/-- Execute the actual initial store, all four ABI root instructions, and all
five Market allocation instructions from the ORIGINAL transaction state. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (headAvailable : 100 ≤ state.world.calldataSize.val)
    (offsetBound : ImportedAbiTupleHead.rawOffset state 0 ≤ 2^64 - 1)
    (tupleAvailable : 4 + ImportedAbiTupleHead.rawOffset state 0 + 256 ≤ state.world.calldataSize.val)
    (sizeBound : state.world.calldataSize.val < Verity.Core.Int256.signBit) :
    execStmtList oracle fields state segment = .continue (completed state) := by
  have initialized := ImportedCreationDecoderAllocation.execute_initial oracle fields state
  have root := ImportedAbiTupleHead.execute oracle fields
    (ImportedCreationDecoderAllocation.initialized state) "_verity_slice_tmp_0_calldata" 3 0 8
    headAvailable offsetBound tupleAvailable sizeBound
  have pointer : ((rootState state).world.memory 64).val = 128 :=
    ImportedCreationDecoderAllocation.initial_pointer state
  have allocation := ImportedCreationDecoderAllocation.execute oracle fields (rootState state) 128
    pointer (by decide)
  rw [segment, SolidityImport.exec_append, SolidityImport.exec_append, initialized]
  change (match execStmtList oracle fields (ImportedCreationDecoderAllocation.initialized state) rootSegment with
    | .continue next => execStmtList oracle fields next ImportedCreationDecoderAllocation.segment
    | outcome => outcome) = _
  rw [root]
  exact allocation

/-- The input tuple pointer comes from original calldata, with no output premise. -/
theorem root_binding (state : DenoteState) :
    lookupValue (completed state).bindings "_verity_slice_tmp_0_calldata" =
      4 + ImportedAbiTupleHead.rawOffset state 0 := by
  rw [completed, ImportedCreationDecoderAllocation.allocated]
  change lookupValue (bindValue (bindValue (rootState state).bindings
    "_verity_slice_tmp_0_memory" 128) "_verity_slice_tmp_0_next" 384) _ = _
  rw [SolidityImport.lookup_bind_other _ _ _ _ (by decide),
    SolidityImport.lookup_bind_other _ _ _ _ (by decide)]
  exact SolidityImport.lookup_bind_same _ _ _

/-- Every byte outside the allocator word retains the original transaction world. -/
theorem byte_frame (state : DenoteState) (query : Nat)
    (outside : query < 64 ∨ 96 ≤ query) :
    (completed state).world.physicalByte query = state.world.physicalByte query := by
  rw [completed, ImportedCreationDecoderAllocation.byte_frame _ _ _ outside]
  exact writePhysicalMemoryValue_byte_outside _ _ _ _ outside

theorem coherent (state : DenoteState) : Coherent (completed state).world :=
  ImportedCreationDecoderAllocation.coherent _ _

theorem free_pointer (state : DenoteState) :
    (completed state).world.memory 64 = Verity.Core.Uint256.ofNat 384 :=
  ImportedCreationDecoderAllocation.free_pointer _ _

end Contracts.SolidityImportSmoke.ImportedCreationDecoderHead
