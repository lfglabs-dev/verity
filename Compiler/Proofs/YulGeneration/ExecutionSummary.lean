import Compiler.Proofs.ExecutionSummary
import Compiler.Proofs.YulGeneration.RuntimeTypes

namespace Compiler.Proofs.YulGeneration

open Compiler.Proofs
open Compiler.Proofs.IRGeneration

/-- Existing Yul and EVMYulLean-projected results expose the common
raw-summary interface without changing either executable semantics. -/
def RawSummary.ofYulResult (result : YulResult) :
    RawSummary Nat IRStorageSlot IRStorageWord (List Nat) :=
  { success := result.success
    returnValue := result.returnValue
    storage := result.finalStorage
    events := result.events }

/-- Refinement seam used by backend proofs: equality of existing result
records implies equality of their checked, typed summaries. -/
theorem RawSummary.ofYulResult_refines_of_eq
    (ir : IRResult) (yul : YulResult)
    (hSuccess : yul.success = ir.success)
    (hReturn : yul.returnValue = ir.returnValue)
    (hStorage : yul.finalStorage = ir.finalStorage)
    (hEvents : yul.events = ir.events) :
    (RawSummary.ofYulResult yul).toExecutionSummary? =
      (RawSummary.ofIRResult ir).toExecutionSummary? := by
  cases yul
  cases ir
  simp_all [RawSummary.ofYulResult, RawSummary.ofIRResult]

end Compiler.Proofs.YulGeneration
