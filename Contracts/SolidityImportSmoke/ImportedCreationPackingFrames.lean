import Contracts.SolidityImportSmoke.ImportedCreationCopySlices
import Compiler.Proofs.IRGeneration.ImportedCreationPacking
import Compiler.Proofs.IRGeneration.ImportedCreationCopyBindings

namespace Contracts.SolidityImportSmoke.ImportedCreationPackingFrames
open Compiler.CompilationModel Denote
open ImportedCreationCopySlices
open Compiler.Proofs.IRGeneration

/-- The actual header loop preserves the payload pointer, byte count and every
local other than its own three temporaries. -/
theorem header_binding (oracle : DenoteOracle) (fields : List Field)
    (initial final : DenoteState) (key : String)
    (indexFresh : "_verity_slice_tmp_27" ≠ key)
    (byteFresh : "_verity_slice_tmp_28" ≠ key)
    (addressFresh : "_verity_slice_tmp_29" ≠ key)
    (executed : execStmt oracle fields initial (ImportedCreationCopySlices.statement false) = .continue final) :
    lookupValue final.bindings key = lookupValue initial.bindings key := by
  exact ImportedCreationCopyBindings.statement oracle fields initial final
    "_verity_slice_tmp_20" "_verity_slice_tmp_23" "_verity_slice_tmp_26"
    "_verity_slice_tmp_27" "_verity_slice_tmp_28" "_verity_slice_tmp_29" key (.literal 11)
    indexFresh byteFresh addressFresh executed

def increment : Stmt := .assignVar "_verity_slice_tmp_26"
  (.add (.localVar "_verity_slice_tmp_26") (.literal 11))

/-- The real statement between the two copies, not a substituted transition. -/
theorem actual_increment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map fun fn => fn.body[86]?).getD none =
      some increment := by rfl

/-- From the real header execution and its invariant, execute the intervening
assignment and derive payload descriptors, count and unchanged physical world. -/
theorem payload_inputs (oracle : DenoteOracle) (fields : List Field)
    (initial header : DenoteState) (hsource psource destination size : Nat)
    (executed : execStmt oracle fields initial (ImportedCreationCopySlices.statement false) = .continue header)
    (copied : AbiCopyLoopInvariant (inputs false hsource destination 0) initial 11 header)
    (source : lookupValue initial.bindings "_verity_slice_tmp_3" = psource)
    (count : lookupValue initial.bindings "_verity_slice_tmp_19" = size) :
    ∃ ready, execStmt oracle fields header increment = .continue ready ∧
      ready.world = header.world ∧ (inputs true psource destination 11).Holds ready ∧
      lookupValue ready.bindings "_verity_slice_tmp_19" = size := by
  let ready : DenoteState := { header with bindings := bindValue header.bindings "_verity_slice_tmp_26" 11 }
  have start : lookupValue header.bindings "_verity_slice_tmp_26" = 0 := copied.1.2.2
  have dest : lookupValue header.bindings "_verity_slice_tmp_23" = destination := copied.1.2.1
  have payload : lookupValue header.bindings "_verity_slice_tmp_3" = psource :=
    (header_binding oracle fields initial header _ (by decide) (by decide) (by decide) executed).trans source
  have length : lookupValue header.bindings "_verity_slice_tmp_19" = size :=
    (header_binding oracle fields initial header _ (by decide) (by decide) (by decide) executed).trans count
  refine ⟨ready, ?_, rfl, ?_, ?_⟩
  · simp only [increment, execStmt, evalExpr, start]
    rfl
  · change lookupValue ready.bindings "_verity_slice_tmp_3" = psource ∧
      lookupValue ready.bindings "_verity_slice_tmp_23" = destination ∧
      lookupValue ready.bindings "_verity_slice_tmp_26" = 11
    simp only [ready, SolidityImport.lookup_bind_other _ _ _ _ (by decide : "_verity_slice_tmp_26" ≠ "_verity_slice_tmp_3"),
      SolidityImport.lookup_bind_other _ _ _ _ (by decide : "_verity_slice_tmp_26" ≠ "_verity_slice_tmp_23"),
      SolidityImport.lookup_bind_same, payload, dest, and_self]
  · simpa only [ready, SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_26" ≠ "_verity_slice_tmp_19")] using length

end Contracts.SolidityImportSmoke.ImportedCreationPackingFrames
