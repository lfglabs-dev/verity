import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopGeometry
import Compiler.Proofs.IRGeneration.NativeSourceDynamicExit

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded NativeSourceDynamicLoopInduction

def tested (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256) :=
  NativeSourceDynamicHeader.s6 cost pre r.x0 r.x1 (r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail)
def exited (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256) :=
  NativeSourceDynamicExit.s11 cost (tested cost r pre tail) r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail

theorem execute_exit (fuel cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (inv : Invariant r pre tail) (done : ¬r.x0 < r.x1) :
    run fuel cost 17 pre = .ok (exited cost r pre tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 6 11 pre _ _
    (NativeSourceDynamicHeader.execute fuel cost pre r.x0 r.x1 (r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail) inv.1 inv.2.1 inv.2.2.1)
    (NativeSourceDynamicExit.execute fuel cost _ r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail inv.1
      (NativeSourceDynamicHeader.exit_pc cost pre r.x0 r.x1 (r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail) inv.2.1 done)
      (NativeSourceDynamicHeader.output_stack cost pre r.x0 r.x1 (r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail)))

theorem exit_endpoint (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (inside : r.x11.toNat ≤ pre.memory.size) : r.x11.toNat ≤ (exited cost r pre tail).memory.size := by
  unfold exited tested
  rw [NativeSourceDynamicExit.memory, NativeSourceDynamicHeader.memory]
  exact inside

theorem exit_pc (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 551) (done : ¬r.x0 < r.x1) :
    (exited cost r pre tail).pc = UInt256.ofNat 573 := by
  exact NativeSourceDynamicExit.finish_pc cost _ r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail
    (NativeSourceDynamicHeader.exit_pc cost pre r.x0 r.x1 (r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail) pc done)

def returned (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256) :=
  exited cost (advance n r) (iterate n cost r pre tail) tail

theorem execute (n fuel cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (countBound : r.x1.toNat < 2 ^ 64) (remaining : r.x0.toNat + n = r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    run fuel cost (62 * n + 17) pre = .ok (returned n cost r pre tail) := by
  have good := NativeSourceDynamicLoopGeometry.good_from_bounds n r countBound (by omega) endpoint
  have finalInv := invariant_iterate n cost r pre tail platform inv good
  have done := NativeSourceDynamicLoopGeometry.terminal n r countBound remaining endpoint
  exact NativeSourceSizedPacking.compose fuel cost (62 * n) 17 pre _ _
    (NativeSourceDynamicLoopGeometry.execute_from_bounds n fuel cost r pre tail platform inv countBound (by omega) endpoint)
    (execute_exit fuel cost (advance n r) (iterate n cost r pre tail) tail finalInv done)

theorem endpoint_inside (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (countBound : r.x1.toNat < 2 ^ 64) (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    r.x11.toNat + 128 * n ≤ (returned n cost r pre tail).memory.size := by
  have good := NativeSourceDynamicLoopGeometry.good_from_bounds n r countBound remaining endpoint
  have finalInv := invariant_iterate n cost r pre tail platform inv good
  have values := NativeSourceDynamicLoopGeometry.advance_values n r (by omega) endpoint
  have inside := exit_endpoint cost (advance n r) (iterate n cost r pre tail) tail finalInv.2.2.2
  rw [values.2] at inside
  exact inside

theorem returned_pc (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (countBound : r.x1.toNat < 2 ^ 64) (remaining : r.x0.toNat + n = r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    (returned n cost r pre tail).pc = UInt256.ofNat 573 := by
  have good := NativeSourceDynamicLoopGeometry.good_from_bounds n r countBound (by omega) endpoint
  have finalInv := invariant_iterate n cost r pre tail platform inv good
  exact exit_pc cost (advance n r) (iterate n cost r pre tail) tail finalInv.2.1
    (NativeSourceDynamicLoopGeometry.terminal n r countBound remaining endpoint)

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopReturn
