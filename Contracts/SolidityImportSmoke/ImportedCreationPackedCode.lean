import Contracts.SolidityImportSmoke.ImportedCreationHeaderPreparation
import Compiler.Proofs.IRGeneration.CreationPackedBytes

namespace Contracts.SolidityImportSmoke.ImportedCreationPackedCode
open Compiler.CompilationModel Denote PhysicalMemory DenoteMemory
open Compiler.Proofs.IRGeneration
open ImportedCreationHeaderPreparation
open Verity.Core.Model

def segment := ImportedCreationHeaderPreparation.segment ++ ImportedCreationAllocatedPacking.segment

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 71).take 17) = some segment := by rfl

/-- The exact header slice of the derived preparation state is the literal
prefix, not an assumed hash or a sampled subset of its bytes. -/
theorem prepared_header (initial ready : DenoteState) (base source size : Nat)
    (prepared : Prepared initial ready base source size) :
    Create2.physicalInitcodeBytes ready.world base 11 = ImportedCreationHeaderAllocation.prefixBytes := by
  have fixed : (⟨((List.range 11).map fun index =>
      ImportedCreationHeaderAllocation.prefixBytes[index]!).toArray⟩ : ByteArray) =
      ImportedCreationHeaderAllocation.prefixBytes := by decide
  refine Eq.trans ?_ fixed
  apply congrArg (fun bytes : List UInt8 => (⟨bytes.toArray⟩ : ByteArray))
  apply List.map_congr_left
  intro index inside
  exact prepared.bytes ⟨index, List.mem_range.mp inside⟩

/-- Both copied inputs are now explicit: actual literal header and the
ORIGINAL pre-preparation physical payload bytes. -/
theorem prepared_code (initial ready : DenoteState) (base source size : Nat)
    (prepared : Prepared initial ready base source size) :
    Create2.physicalInitcodeBytes
      ((ready.world.copyPhysicalBytes ready.world.physicalByte (base + 32) base 11).copyPhysicalBytes
        ready.world.physicalByte (base + 32 + 11) source size) (base + 32) (11 + size) =
      ImportedCreationHeaderAllocation.prefixBytes ++ Create2.physicalInitcodeBytes initial.world source size := by
  rw [CreationPackedBytes.copied_code]
  change Create2.physicalInitcodeBytes ready.world base 11 ++
    Create2.physicalInitcodeBytes ready.world source size = _
  rw [prepared_header initial ready base source size prepared]
  congr 1
  exact CreationRelocatedCopies.relocated_slice ready.world initial.world source source size prepared.original

/-- Execute all seventeen actual imported statements. No desired intermediate
memory, header bytes, zero buffer, pointer or total-size binding is supplied.
The output is EXACT literal-prefix ++ original payload, for arbitrary length. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source size : Nat) (baseAligned : base % 32 = 0) (sourceAligned : source % 32 = 0)
    (pastPointer : 96 ≤ source) (beforeHeader : source + size ≤ base)
    (pointer : (state.world.memory 64).val = base)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = source)
    (length : lookupValue state.bindings "_verity_slice_tmp_19" = size)
    (budget : base + 32 + 32 * ((11 + size + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle fields state segment = .continue final ∧
      Create2.physicalInitcodeBytes final.world (base + 32) (11 + size) =
        ImportedCreationHeaderAllocation.prefixBytes ++ Create2.physicalInitcodeBytes state.world source size := by
  have headerBound : base + 32 ≤ 2^64 - 1 := by omega
  have range : 11 + size < Verity.Core.Uint256.modulus := by
    have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
    omega
  obtain ⟨ready, preparation, prepared⟩ := prepare oracle fields state base source size pastPointer beforeHeader
    pointer headerBound payload length range
  have geometry : ImportedCreationAllocatedPacking.Geometry base source (base + 32) size :=
    ⟨baseAligned, sourceAligned, by omega, by omega, by omega⟩
  obtain ⟨final, packing, code⟩ := ImportedCreationOriginalSnapshots.execute oracle fields ready
    base source (base + 32) size geometry (by omega) pastPointer prepared.pointer prepared.total
    prepared.header prepared.payload prepared.count budget
  refine ⟨final, ?_, code.trans (prepared_code state ready base source size prepared)⟩
  rw [segment, SolidityImport.exec_append, preparation]
  exact packing

end Contracts.SolidityImportSmoke.ImportedCreationPackedCode
