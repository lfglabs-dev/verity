import Compiler.SolidityImport.Transactions
import Verity.Core.Model.DenoteByteExternalCalls

/-! Bridge byte-call failure into the existing exact Denote transaction
finisher. This does not add an importer lowering or synthesize returndata for
a payload-free Denote failure. -/
namespace Compiler.CompilationModel.SolidityImport.ByteCallTransactions

open DenoteByteExternalCalls

structure TracedFrameResult where
  frame : Transactions.FrameResult
  touched : List Verity.StorageKey

/-- A high-level caller that propagates a failed child call reverts its entire
frame, including writes performed before the child call. Child and caller
access traces remain available for differential observation. A successful child
response cannot be reclassified as a bubbled failure. -/
def bubble (entry : Verity.ContractState) (observed : Observation) :
    Except String TracedFrameResult := do
  if observed.success then throw "cannot bubble a successful external call"
  let frame ← Transactions.finishFrame entry (.revertWithData observed.state.returndata)
  pure { frame, touched := observed.state.touched }

theorem bubble_failure (entry : Verity.ContractState) (observed : Observation)
    (hfailed : observed.success = false) :
    bubble entry observed = .ok
      { frame := { success := false, data := observed.state.returndata, world := entry }
        touched := observed.state.touched } := by
  simp [bubble, hfailed, Transactions.finishFrame]
  rfl

theorem bubble_success_rejected (entry : Verity.ContractState) (observed : Observation)
    (hsuccess : observed.success = true) :
    bubble entry observed = .error "cannot bubble a successful external call" := by
  simp [bubble, hsuccess]
  rfl

end Compiler.CompilationModel.SolidityImport.ByteCallTransactions
