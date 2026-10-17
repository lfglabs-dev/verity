import Compiler.SolidityImport.AbiPhysicalMemory
import Compiler.Proofs.Frames

namespace SolidityImportSmoke.PhysicalMemoryFrameChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote

def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
def state : DenoteState := { world := Verity.defaultState, bindings := [] }

/-- Distinct starting offsets do not imply disjoint physical word windows. -/
theorem overlapping_window_changes :
    (match execStmt oracle [] state (.mstore (.literal 0) (.literal 1)) with
    | .continue after => (after.world.memory 1).val
    | _ => 0) = 256 := by decide

/-- The computable footprint covers all 32 written bytes. -/
theorem store_footprint_is_32_bytes :
    Compiler.Proofs.Frames.Stmt.writeFootprint (.mstore (.literal 0) (.literal 1)) =
      some [.mem 0 32] := by rfl

/-- An offset inside the stored word cannot receive a disjoint frame. -/
theorem overlapping_byte_not_disjoint :
    ¬ Compiler.Proofs.Frames.Resource.Disjoint (.mem 1 2) (.mem 0 32) := by
  change ¬ (2 ≤ 0 ∨ 32 ≤ 1)
  decide

/-- The byte frame covers arbitrary inputs, not only coherent aligned worlds. -/
theorem outside_byte_preserved (oracle : DenoteOracle) (fields : List Field)
    (before after : DenoteState) (offset value : Expr) (address word query : Nat)
    (resolvedOffset : evalExpr oracle fields before offset = some address)
    (resolvedValue : evalExpr oracle fields before value = some word)
    (executed : execStmt oracle fields before (.mstore offset value) = .continue after)
    (outside : query < address ∨ address + 32 ≤ query) :
    after.world.physicalByte query = before.world.physicalByte query :=
  execStmt_mstore_physical_byte_frame oracle fields before after offset value
    address word query resolvedOffset resolvedValue executed outside

end SolidityImportSmoke.PhysicalMemoryFrameChecks
