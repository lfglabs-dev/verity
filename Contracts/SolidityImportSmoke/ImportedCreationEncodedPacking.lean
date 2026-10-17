import Contracts.SolidityImportSmoke.ImportedCreationAbiLayout

namespace Contracts.SolidityImportSmoke.ImportedCreationEncodedPacking
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration ImportedCreationPrelude ImportedCreationAbiLayout

theorem payload_binding (state : DenoteState) (source head : Nat) (coherent : Coherent state.world)
    (pastPointer : 96 ≤ source) (before : source + 128 ≤ head)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 ≤ head) :
    lookupValue (completed state source head).bindings "_verity_slice_tmp_3" = head := by
  rw [completed, ImportedCreationFieldFrames.binding _ _ _ _ _ (by simp [ImportedCreationHeadFields.lastEntries])]
  exact (array_bindings state source head coherent pastPointer before arrayPast arrayBefore).2

def segment := fullSegment ++ ImportedCreationLength.segment

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 39).take 49) = some segment := by rfl

/-- Execute ALL49actualinstructions: completeMarketencoder, realpointerlength,
headerpreparation, packedallocation and both bytecopyloops. FinalcodeisEXACTLY
the11byteliteralprefix++thecompleteABIbytesofORIGINALencoderentryinputs. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source head : Nat) (coherent : Coherent state.world)
    (pointer : (state.world.memory 64).val = head)
    (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (pastPointer : 96 ≤ source) (before : source + 256 ≤ head) (aligned : head % 32 = 0)
    (arrayPast : 96 ≤ ImportedCreationArrayDescriptors.pointer state source)
    (arrayBefore : ImportedCreationArrayDescriptors.pointer state source + 32 +
      32 * ImportedCreationArrayDescriptors.count state source ≤ head)
    (sources : ∀ i < ImportedCreationArrayDescriptors.count state source,
      96 ≤ ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i ∧
      ImportedAbiArray.sourceAt state.world (ImportedCreationArrayDescriptors.pointer state source + 32) i + 128 ≤ head)
    (budget : head + payloadSize state source + 32 + 32 * ((11 + payloadSize state source + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle fields state segment = .continue final ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes final.world (head + payloadSize state source + 32)
        (11 + payloadSize state source) = ImportedCreationHeaderAllocation.prefixBytes ++ abiBytes state source := by
  have size : payloadSize state source = 320 + 128 * ImportedCreationArrayDescriptors.count state source := rfl
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have encoded := execute_full oracle fields state source head coherent pointer held pastPointer before arrayPast arrayBefore
    (fun i live => (sources i live).2) (by omega)
  have free : ((completed state source head).world.memory 64).val = head + payloadSize state source := by
    rw [completed_pointer state source head (by omega), Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have baseAligned : (head + payloadSize state source) % 32 = 0 := by omega
  have heldHead := payload_binding state source head coherent pastPointer (by omega) arrayPast (by omega)
  obtain ⟨final, run, code⟩ := ImportedCreationLength.execute oracle fields (completed state source head)
    (head + payloadSize state source) head baseAligned aligned (by omega) (by omega) free heldHead (by omega)
  have length : head + payloadSize state source - head = payloadSize state source := by omega
  rw [length, payload_code state source head coherent pastPointer before arrayPast arrayBefore sources] at code
  refine ⟨final, ?_, code⟩
  rw [segment, SolidityImport.exec_append, encoded]
  exact run

end Contracts.SolidityImportSmoke.ImportedCreationEncodedPacking
