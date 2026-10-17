import Compiler.Proofs.IRGeneration.NativePairedCallerFuel

namespace Compiler.Proofs.IRGeneration.NativeJumpScannerFrame
open EvmYul

/-- The native scanner never removes a previously certified destination. -/
theorem preserves (code : ByteArray) (fuel pc : Nat) (found : Array UInt256)
    (destination : UInt256) (present : destination ∈ found) :
    destination ∈ EVM.D_J_aux code fuel pc found := by
  induction fuel generalizing pc found with
  | zero => exact present
  | succ fuel ih =>
    simp only [EVM.D_J_aux]
    split
    · split
      · exact present
      · apply ih
        split
        · exact Array.mem_push_of_mem _ present
        · exact present
    · exact present

end Compiler.Proofs.IRGeneration.NativeJumpScannerFrame
