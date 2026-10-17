import Contracts.SolidityImportSmoke.ImportedCreationArrayLoop

namespace Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory

def segment : List Stmt := SolidityImport.AbiEncoding.reserve
  "_verity_slice_tmp_3" "_verity_slice_tmp_4" (.literal 288) ++
  [.mstore (.localVar "_verity_slice_tmp_3") (.literal 32)]

def allocated (state : DenoteState) (head : Nat) : DenoteState :=
  { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_3" head) "_verity_slice_tmp_4" (head + 288)
    world := ((state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (head + 288))).writePhysicalMemoryValue
      head (Verity.Core.Uint256.ofNat 32)) }

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 6) = some segment := by rfl

/-- Actual9-word head reservation and root tuple-offset store, with exact whole
state, free-pointer update, expansion and all overlapping word observations. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (head : Nat) (pointer : (state.world.memory 64).val = head)
    (budget : head + 288 ≤ 2^64 - 1) :
    execStmtList oracle fields state segment = .continue (allocated state head) := by
  let reserved : DenoteState := { state with
    bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_3" head) "_verity_slice_tmp_4" (head + 288)
    world := state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (head + 288)) }
  have allocation := execStmtList_reserve_physical oracle fields state "_verity_slice_tmp_3" "_verity_slice_tmp_4"
    (.literal 288) head 288 pointer (by decide) (by rfl) budget
  have descriptor : lookupValue reserved.bindings "_verity_slice_tmp_3" = head := by
    simp only [reserved, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_4" "_verity_slice_tmp_3" _ (by decide),
      SolidityImport.lookup_bind_same]
  have stored := execStmt_mstore_physical oracle fields reserved (.localVar "_verity_slice_tmp_3")
    (.literal 32) head 32 (by simp only [evalExpr, descriptor]) (by rfl)
  rw [segment, SolidityImport.exec_append, allocation]
  exact (SolidityImport.exec_singleton oracle fields reserved _).trans stored

/-- The root tuple offset is32 because the real imported instruction stores it. -/
theorem root_word (state : DenoteState) (head : Nat) :
    (allocated state head).world.memory head = Verity.Core.Uint256.ofNat 32 := by
  exact writePhysicalMemoryValue_at _ _ _

/-- Both actual stores preserve every input byte beyond the free-pointer word
and before the output head. -/
theorem input_byte (state : DenoteState) (head query : Nat) (pastPointer : 96 ≤ query) (before : query < head) :
    (allocated state head).world.physicalByte query = state.world.physicalByte query := by
  rw [allocated, writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inl before),
    writePhysicalMemoryValue_byte_outside _ _ _ _ (Or.inr pastPointer)]

/-- In particular, full input word windows retain their ORIGINAL observations. -/
theorem input_word (state : DenoteState) (head query : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ query) (before : query + 32 ≤ head) :
    (allocated state head).world.memory query = state.world.memory query := by
  apply Compiler.Proofs.IRGeneration.ImportedAbiArray.word_of_bytes state.world _ query coherent
    (writePhysicalMemoryValue_coherent _ _ _)
  intro offset
  exact input_byte state head (query + offset.val) (by omega) (by have := offset.isLt; omega)

/-- The root word cannot clobber the free-pointer word at64..95. -/
theorem free_pointer (state : DenoteState) (head : Nat) (pastPointer : 96 ≤ head) :
    (allocated state head).world.memory 64 = Verity.Core.Uint256.ofNat (head + 288) := by
  change ((state.world.writePhysicalMemoryValue 64 (Verity.Core.Uint256.ofNat (head + 288))).writePhysicalMemoryWord
    head (valueWord (Verity.Core.Uint256.ofNat 32))).memory 64 = _
  rw [writePhysicalMemoryWord_outside _ _ _ _
    (writePhysicalMemoryValue_coherent state.world 64 (Verity.Core.Uint256.ofNat (head + 288))) (Or.inl pastPointer)]
  exact writePhysicalMemoryValue_at _ _ _

end Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation
