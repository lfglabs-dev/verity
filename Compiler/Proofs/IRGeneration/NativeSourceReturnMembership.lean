import Compiler.Proofs.IRGeneration.NativeSourceReturnScannerPart9

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnMembership
open EvmYul

def found : Array UInt256 := #[UInt256.ofNat 18, UInt256.ofNat 50, UInt256.ofNat 91, UInt256.ofNat 95, UInt256.ofNat 191, UInt256.ofNat 210, UInt256.ofNat 292, UInt256.ofNat 323, UInt256.ofNat 381, UInt256.ofNat 395, UInt256.ofNat 551, UInt256.ofNat 632, UInt256.ofNat 681, UInt256.ofNat 703, UInt256.ofNat 718, UInt256.ofNat 786, UInt256.ofNat 806, UInt256.ofNat 862, UInt256.ofNat 894]

theorem scanned : EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) =
    EVM.D_J_aux NativeSourceAbiWrite.code 346 895 found := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  unfold EVM.D_J
  rw [size]
  change EVM.D_J_aux NativeSourceAbiWrite.code ((346+496+72)+63) 0 #[] = _
  rw [NativeSourceJumpDestinations.scanned_prefix, NativeSourceReturnScannerFirst.scanned_to_210]
  rw [NativeSourceReturnScannerPart1.scanned_block]
  rw [NativeSourceReturnScannerPart2.scanned_block]
  rw [NativeSourceReturnScannerPart3.scanned_block]
  rw [NativeSourceReturnScannerPart4.scanned_block]
  rw [NativeSourceReturnScannerPart5.scanned_block]
  rw [NativeSourceReturnScannerPart6.scanned_block]
  rw [NativeSourceReturnScannerPart7.scanned_block]
  rw [NativeSourceReturnScannerPart8.scanned_block]
  rw [NativeSourceReturnScannerPart9.scanned_block]
  rfl

theorem return_destinations (ret : UInt256)
    (selected : ret ∈ [UInt256.ofNat 191, UInt256.ofNat 210, UInt256.ofNat 381,
      UInt256.ofNat 395, UInt256.ofNat 862, UInt256.ofNat 894]) :
    ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0) := by
  rw [scanned]
  apply NativeJumpScannerFrame.preserves
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [found]

end Compiler.Proofs.IRGeneration.NativeSourceReturnMembership
