import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopReturn
import Compiler.Proofs.IRGeneration.NativeSourcePrecontainedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicMappedEndpoint
open EvmYul NativeSourceDynamicLoopInduction

abbrev mask : UInt256 := (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) - UInt256.ofNat 1

theorem stable_source_base (n : Nat) (r : Registers) :
    (advance n r).x7 = r.x7 ∧ (advance n r).x9 = r.x9 := by
  induction n generalizing r with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact ih r.next

theorem source_value (n : Nat) (r : Registers) (source : r.x7.toNat = r.x9.toNat + 32) :
    (advance n r).x7.toNat = (advance n r).x9.toNat + 32 := by
  rw [(stable_source_base n r).1, (stable_source_base n r).2]
  exact source

theorem ordered (n : Nat) (r : Registers)
    (indexBound : r.x0.toNat + n < 2 ^ 256)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64)
    (initial : r.x9.toNat + 32 ≤ r.x11.toNat) :
    (advance n r).x9.toNat + 32 ≤ (advance n r).x11.toNat := by
  rw [(stable_source_base n r).2, (NativeSourceDynamicLoopGeometry.advance_values n r indexBound endpoint).2]
  omega

theorem endpoint_inside (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (countBound : r.x1.toNat < 2 ^ 64) (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    (advance n r).x11.toNat ≤ (NativeSourceDynamicLoopReturn.returned n cost r pre tail).memory.size := by
  rw [(NativeSourceDynamicLoopGeometry.advance_values n r (by omega) endpoint).2]
  exact NativeSourceDynamicLoopReturn.endpoint_inside n cost r pre tail platform inv countBound remaining endpoint

theorem output_stack (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256) :
    let q := advance n r
    (NativeSourceDynamicLoopReturn.returned n cost r pre tail).stack =
      mask :: q.x11 :: q.x9 :: q.x3 :: q.x4 :: q.x5 :: q.x6 :: q.x7 :: q.x8 :: q.x9 :: q.x10 ::
        mask :: q.x12 :: q.x13 :: q.x14 :: q.x15 :: tail := by
  dsimp only
  unfold NativeSourceDynamicLoopReturn.returned NativeSourceDynamicLoopReturn.exited
  exact NativeSourceDynamicExit.output_stack cost _ (advance n r).x0 (advance n r).x1 (advance n r).x2
    (advance n r).x3 (advance n r).x4 (advance n r).x5 (advance n r).x6 (advance n r).x7 (advance n r).x8
    (advance n r).x9 (advance n r).x10 (advance n r).x11 (advance n r).x12 (advance n r).x13
    (advance n r).x14 (advance n r).x15 tail

end Compiler.Proofs.IRGeneration.NativeSourceDynamicMappedEndpoint
