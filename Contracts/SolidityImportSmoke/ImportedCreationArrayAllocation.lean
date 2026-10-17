import Contracts.SolidityImportSmoke.ImportedCreationLength

namespace Contracts.SolidityImportSmoke.ImportedCreationArrayAllocation
open Compiler.CompilationModel Denote

def sizeExpr : Expr := .add (.literal 32) (.mul (.localVar "_verity_slice_tmp_9") (.literal 128))
def segment := SolidityImport.AbiEncoding.reserve "_verity_slice_tmp_11" "_verity_slice_tmp_12" sizeExpr

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 54).take 5) = some segment := by rfl

/-- Each dynamic Market collateral occupies its actual four-word ABI stride.
All multiplication/addition wrap conditions follow from the allocator bound. -/
theorem evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base count : Nat) (held : lookupValue state.bindings "_verity_slice_tmp_9" = count)
    (budget : base + (32 + 128 * count) ≤ 2^64 - 1) :
    evalExpr oracle fields state sizeExpr = some (32 + 128 * count) := by
  have ceiling : 2^64 - 1 < Verity.Core.Uint256.modulus := by decide
  have small : count < Verity.Core.Uint256.modulus := by omega
  have stride : count * 128 < Verity.Core.Uint256.modulus := by omega
  have total : 32 + 128 * count < Verity.Core.Uint256.modulus := by omega
  simp only [sizeExpr, evalExpr, held]
  change some ((32 + (count % Verity.Core.Uint256.modulus * 128) % Verity.Core.Uint256.modulus % Verity.Core.Uint256.modulus) %
    Verity.Core.Uint256.modulus) = _
  rw [Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt stride, Nat.mod_eq_of_lt stride, Nat.mul_comm count 128, Nat.mod_eq_of_lt total]

/-- Exact actual array-tail reservation, with all source state and descriptors
retained apart from the generated bindings and real free-pointer store. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base count : Nat) (pointer : (state.world.memory 64).val = base)
    (held : lookupValue state.bindings "_verity_slice_tmp_9" = count)
    (budget : base + (32 + 128 * count) ≤ 2^64 - 1) :
    execStmtList oracle fields state segment = .continue
      { state with
        bindings := bindValue (bindValue state.bindings "_verity_slice_tmp_11" base)
          "_verity_slice_tmp_12" (base + (32 + 128 * count))
        world := state.world.writePhysicalMemoryValue 64
          (Verity.Core.Uint256.ofNat (base + (32 + 128 * count))) } := by
  apply execStmtList_reserve_physical oracle fields state "_verity_slice_tmp_11" "_verity_slice_tmp_12"
    sizeExpr base (32 + 128 * count) pointer (by decide) _ budget
  apply evaluated oracle fields _ base count _ budget
  simpa only [SolidityImport.lookup_bind_other _ _ _ _
    (by decide : "_verity_slice_tmp_11" ≠ "_verity_slice_tmp_9")] using held

end Contracts.SolidityImportSmoke.ImportedCreationArrayAllocation
