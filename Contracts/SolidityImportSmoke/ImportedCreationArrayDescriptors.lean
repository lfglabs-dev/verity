import Compiler.Proofs.IRGeneration.ImportedAbiWordBinding
import Contracts.SolidityImportSmoke.ImportedCreationHeadAllocation

namespace Contracts.SolidityImportSmoke.ImportedCreationArrayDescriptors
open Compiler.CompilationModel Denote PhysicalMemory
open Compiler.Proofs.IRGeneration

def pointer (state : DenoteState) (source : Nat) := (state.world.memory (source + 96)).val
def count (state : DenoteState) (source : Nat) := (state.world.memory (pointer state source)).val

def segment : List Stmt :=
  [.letVar "_verity_slice_tmp_8" (.mload (.add (.localVar "_verity_slice_tmp_0_memory") (.literal 96))),
   .letVar "_verity_slice_tmp_9" (.mload (.localVar "_verity_slice_tmp_8")),
   .letVar "_verity_slice_tmp_10" (.add (.localVar "_verity_slice_tmp_8") (.literal 32))]

def extracted (state : DenoteState) (source : Nat) : DenoteState :=
  { state with bindings := bindValue (bindValue (bindValue state.bindings "_verity_slice_tmp_8" (pointer state source))
    "_verity_slice_tmp_9" (count state source)) "_verity_slice_tmp_10" (pointer state source + 32) }

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 51).take 3) = some segment := by rfl

/-- Actual3instruction extraction reads the pointer/count from physical-world
word observations. Neither a count local nor an invented array pointer is input. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (source : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_0_memory" = source)
    (sourceBound : source + 96 < Verity.Core.Uint256.modulus)
    (pointerBound : pointer state source + 32 < Verity.Core.Uint256.modulus) :
    execStmtList oracle fields state segment = .continue (extracted state source) := by
  have address := ImportedAbiWordBinding.add_evaluated oracle fields state
    (.localVar "_verity_slice_tmp_0_memory") (.literal 96) source 96
    (by simp only [evalExpr, held]) (by rfl) sourceBound
  have first : evalExpr oracle fields state (.mload (.add (.localVar "_verity_slice_tmp_0_memory") (.literal 96))) =
      some (pointer state source) := by rw [evalExpr, address]; rfl
  let one := { state with bindings := bindValue state.bindings "_verity_slice_tmp_8" (pointer state source) }
  let two := { one with bindings := bindValue one.bindings "_verity_slice_tmp_9" (count state source) }
  have second : evalExpr oracle fields one (.mload (.localVar "_verity_slice_tmp_8")) = some (count state source) := by
    simp only [evalExpr, one, SolidityImport.lookup_bind_same]
    rfl
  have third := ImportedAbiWordBinding.add_evaluated oracle fields two (.localVar "_verity_slice_tmp_8") (.literal 32)
    (pointer state source) 32
    (by simp only [evalExpr, two, one, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_9" "_verity_slice_tmp_8" _ (by decide), SolidityImport.lookup_bind_same])
    (by rfl) pointerBound
  rw [segment, SolidityImport.exec_let_cons, first]
  change execStmtList oracle fields one _ = _
  rw [SolidityImport.exec_let_cons, second]
  change execStmtList oracle fields two _ = _
  rw [SolidityImport.exec_let_cons, third]
  rfl

/-- The resulting descriptor locals are derived, including data-base=pointer+32. -/
theorem descriptors (state : DenoteState) (source : Nat) :
    lookupValue (extracted state source).bindings "_verity_slice_tmp_8" = pointer state source ∧
    lookupValue (extracted state source).bindings "_verity_slice_tmp_9" = count state source ∧
    lookupValue (extracted state source).bindings "_verity_slice_tmp_10" = pointer state source + 32 := by
  simp only [extracted, SolidityImport.lookup_bind_other _ "_verity_slice_tmp_10" "_verity_slice_tmp_8" _ (by decide),
    SolidityImport.lookup_bind_other _ "_verity_slice_tmp_10" "_verity_slice_tmp_9" _ (by decide),
    SolidityImport.lookup_bind_other _ "_verity_slice_tmp_9" "_verity_slice_tmp_8" _ (by decide), SolidityImport.lookup_bind_same,
    and_self]

/-- All other descriptors and the ENTIRE world are untouched by extraction. -/
theorem binding_frame (state : DenoteState) (source : Nat) (key : String)
    (n8 : "_verity_slice_tmp_8" ≠ key) (n9 : "_verity_slice_tmp_9" ≠ key) (n10 : "_verity_slice_tmp_10" ≠ key) :
    lookupValue (extracted state source).bindings key = lookupValue state.bindings key := by
  rw [extracted, SolidityImport.lookup_bind_other _ _ _ _ n10,
    SolidityImport.lookup_bind_other _ _ _ _ n9, SolidityImport.lookup_bind_other _ _ _ _ n8]

end Contracts.SolidityImportSmoke.ImportedCreationArrayDescriptors
