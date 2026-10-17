import Contracts.SolidityImportSmoke.ImportedCreationPackedCode

namespace Contracts.SolidityImportSmoke.ImportedCreationLength
open Compiler.CompilationModel Denote
open Verity.Core.Model

def expression : Expr := .sub (.mload (.literal 64)) (.localVar "_verity_slice_tmp_3")
def binding : Stmt := .letVar "_verity_slice_tmp_19" expression
def segment := binding :: ImportedCreationPackedCode.segment

theorem actual_segment :
    (ImportedCreationPrefixFrames.imported.model.functions.head?.map
      fun fn => (fn.body.drop 70).take 18) = some segment := by rfl

/-- The real unsigned subtraction computes the original buffer length once
actual allocator monotonicity has established that the source precedes it. -/
theorem evaluated (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source : Nat) (pointer : (state.world.memory 64).val = base)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = source)
    (ordered : source ≤ base) :
    evalExpr oracle fields state expression = some (base - source) := by
  have baseBound : base < Verity.Core.Uint256.modulus := pointer ▸ (state.world.memory 64).isLt
  have sourceBound : source < Verity.Core.Uint256.modulus := by omega
  have read : evalExpr oracle fields state (.mload (.literal 64)) = some base := by
    change some (state.world.memory 64).val = some base
    rw [pointer]
  rw [expression, evalExpr, read]
  simp only [evalExpr, payload]
  change some ((Verity.Core.Uint256.ofNat base - Verity.Core.Uint256.ofNat source).val) = _
  have noWrap : (Verity.Core.Uint256.ofNat source).val ≤ (Verity.Core.Uint256.ofNat base).val := by
    simpa only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt baseBound, Nat.mod_eq_of_lt sourceBound] using ordered
  rw [Verity.Core.Uint256.sub_eq_of_le noWrap]
  simp only [Verity.Core.Uint256.val_ofNat, Nat.mod_eq_of_lt baseBound, Nat.mod_eq_of_lt sourceBound]

/-- Actual size-binding execution, retaining the whole input memory/context. -/
theorem step (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source : Nat) (pointer : (state.world.memory 64).val = base)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = source) (ordered : source ≤ base) :
    execStmt oracle fields state binding = .continue
      { state with bindings := bindValue state.bindings "_verity_slice_tmp_19" (base - source) } := by
  simp only [binding, execStmt, evaluated oracle fields state base source pointer payload ordered]

/-- The actual eighteen-statement segment derives size from the free pointer.
No supplied payload count/total/header/output memory is a premise. -/
theorem execute (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (base source : Nat) (baseAligned : base % 32 = 0) (sourceAligned : source % 32 = 0)
    (pastPointer : 96 ≤ source) (ordered : source ≤ base)
    (pointer : (state.world.memory 64).val = base)
    (payload : lookupValue state.bindings "_verity_slice_tmp_3" = source)
    (budget : base + 32 + 32 * ((11 + (base - source) + 31) / 32) ≤ 2^64 - 1) :
    ∃ final, execStmtList oracle fields state segment = .continue final ∧
      Create2.physicalInitcodeBytes final.world (base + 32) (11 + (base - source)) =
        ImportedCreationHeaderAllocation.prefixBytes ++ Create2.physicalInitcodeBytes state.world source (base - source) := by
  let ready : DenoteState := { state with bindings := bindValue state.bindings "_verity_slice_tmp_19" (base - source) }
  have retained : lookupValue ready.bindings "_verity_slice_tmp_3" = source := by
    simpa only [ready, SolidityImport.lookup_bind_other _ _ _ _
      (by decide : "_verity_slice_tmp_19" ≠ "_verity_slice_tmp_3")] using payload
  obtain ⟨final, run, code⟩ := ImportedCreationPackedCode.execute oracle fields ready base source (base - source)
    baseAligned sourceAligned pastPointer (by omega) pointer retained
    (SolidityImport.lookup_bind_same _ _ _) budget
  refine ⟨final, ?_, code⟩
  simp only [segment, execStmtList, step oracle fields state base source pointer payload ordered]
  exact run

end Contracts.SolidityImportSmoke.ImportedCreationLength
