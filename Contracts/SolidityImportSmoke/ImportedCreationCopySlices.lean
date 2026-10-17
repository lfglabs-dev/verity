import Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames
import Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes

namespace Contracts.SolidityImportSmoke.ImportedCreationCopySlices
open Compiler.CompilationModel Denote PhysicalMemory
open Compiler.Proofs.IRGeneration.ImportedCreationCopyBytes

def inputs (payload : Bool) (source destination start : Nat) : AbiCopyInputs :=
  { sourceName := if payload then "_verity_slice_tmp_3" else "_verity_slice_tmp_20"
    destinationName := "_verity_slice_tmp_23", startName := "_verity_slice_tmp_26"
    source, destination, start }

def indexName (payload : Bool) := if payload then "_verity_slice_tmp_30" else "_verity_slice_tmp_27"
def byteName (payload : Bool) := if payload then "_verity_slice_tmp_31" else "_verity_slice_tmp_28"
def addressName (payload : Bool) := if payload then "_verity_slice_tmp_32" else "_verity_slice_tmp_29"
def sizeExpr (payload : Bool) : Expr := if payload then .localVar "_verity_slice_tmp_19" else .literal 11

def statement (payload : Bool) : Stmt :=
  let names := inputs payload 0 0 0
  SolidityImport.AbiEncoding.copyBytes (.localVar names.sourceName)
    (.localVar names.destinationName) (.localVar names.startName) (sizeExpr payload)
    (indexName payload) (byteName payload) (addressName payload)

/-- Both packing loops are exactly the generated helper whose interpreter
semantics have already been proved, not a handwritten replacement. -/
theorem actual_node (payload : Bool) :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => fn.body[if payload then 87 else 85]?).getD none = some (statement payload) := by
  cases payload <;> rfl

/-- Actual imported header/payload loop execution yields the original source
snapshot as physical code. Runtime input obligations are explicit. -/
theorem actual_slice (payload : Bool) (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (source destination start size : Nat)
    (evaluated : evalExpr oracle fields state (sizeExpr payload) = some size)
    (coherent : Coherent state.world) (held : (inputs payload source destination start).Holds state)
    (sourceAligned : source % 32 = 0) (destinationAligned : destination % 32 = 0)
    (sourceBound : source + size < Verity.Core.Uint256.modulus)
    (destinationBound : destination + (start + size) < Verity.Core.Uint256.modulus)
    (disjoint : source + size ≤ destination + start ∨ destination + start + size ≤ source)
    (zero : ∀ index, index < size → abiMemoryByte state.world.memory (destination + start + index) = 0) :
    ∃ after, execStmt oracle fields state (statement payload) = .continue after ∧
      AbiCopyLoopInvariant (inputs payload source destination start) state size after ∧
      Verity.Core.Model.Create2.physicalInitcodeBytes after.world (destination + start) size =
        Verity.Core.Model.Create2.physicalInitcodeBytes state.world source size := by
  exact executed_slice oracle fields (inputs payload source destination start) state (sizeExpr payload)
    (indexName payload) (byteName payload) (addressName payload) size evaluated coherent held
    (by cases payload <;> simp [AbiCopyInputs.Fresh, inputs, indexName])
    (by cases payload <;> simp [AbiCopyInputs.Fresh, inputs, byteName])
    (by cases payload <;> simp [AbiCopyInputs.Fresh, inputs, addressName])
    (by cases payload <;> decide) (by cases payload <;> decide) (by cases payload <;> decide)
    sourceAligned destinationAligned sourceBound destinationBound disjoint zero

end Contracts.SolidityImportSmoke.ImportedCreationCopySlices
