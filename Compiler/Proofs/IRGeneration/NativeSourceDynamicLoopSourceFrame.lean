import Compiler.Proofs.IRGeneration.NativeSourceDynamicElementSourceFrame
import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopSourceFrame
open EvmYul NativeSourceDynamicLoopInduction

theorem suffix_read_below (cost : Nat) (pre : EVM.State)
    (source mask dest spare x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256)
    (tail : Stack UInt256) (start length : Nat) (platform : 64 ≤ System.Platform.numBits)
    (destBound : dest.toNat + 96 < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ dest.toNat) :
    (NativeSourceDynamicIterationSuffix.returned cost pre source mask dest spare
      x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  rw [NativeSourceDynamicIterationSuffix.memory]
  exact NativeSourceDynamicElementSourceFrame.read_below cost pre source mask dest spare
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: tail)
    start length platform destBound positive bounded inside below

theorem ready_memory (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256) :
    (NativeSourceDynamicBody.ready cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).memory = pre.memory := by
  rfl

theorem body_read_below (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (start length : Nat) (platform : 64 ≤ System.Platform.numBits)
    (destBound : r.x11.toNat + 96 < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ r.x11.toNat) :
    (NativeSourceDynamicBody.returned cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have insideReady : start + length ≤ (NativeSourceDynamicBody.ready cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).memory.size := by
    rw [ready_memory]; exact inside
  have frame := suffix_read_below cost
    (NativeSourceDynamicBody.ready cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail)
    r.x2 NativeSourceDynamicBody.mask r.x11 (UInt256.ofNat 128)
    (UInt256.ofNat 1) r.x0 r.x1 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x2 r.x12
    (r.x13 :: r.x14 :: r.x15 :: tail) start length platform destBound positive bounded insideReady below
  change (NativeSourceDynamicBody.returned cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).memory.readWithPadding start length = _ at frame
  rw [ready_memory] at frame
  exact frame

theorem step_read_below (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (start length : Nat) (platform : 64 ≤ System.Platform.numBits)
    (destBound : r.x11.toNat + 96 < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ r.x11.toNat) :
    (r.step cost pre tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have insideTested : start + length ≤ (NativeSourceDynamicIteration.tested cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).memory.size := by
    rw [NativeSourceDynamicHeader.memory]; exact inside
  have frame := body_read_below cost r (NativeSourceDynamicIteration.tested cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail)
    tail start length platform destBound positive bounded insideTested below
  change (r.step cost pre tail).memory.readWithPadding start length = _ at frame
  rw [NativeSourceDynamicHeader.memory] at frame
  exact frame

theorem iterate_read_below (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (start length : Nat) (platform : 64 ≤ System.Platform.numBits)
    (inv : Invariant r pre tail) (good : Good n r)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (below : start + length ≤ r.x11.toNat) :
    (iterate n cost r pre tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  induction n generalizing r pre with
  | zero => rfl
  | succ n ih =>
    have destBound : r.x11.toNat + 96 < 2 ^ 64 := by have bound := good.2.1; omega
    have nextInv := step_invariant cost r pre tail platform inv good.2.1
    have nextBelow : start + length ≤ r.next.x11.toNat := by
      rw [next_endpoint r good.2.1]
      omega
    have rest := ih r.next (r.step cost pre tail) nextInv good.2.2 nextBelow
    exact rest.trans (step_read_below cost r pre tail start length platform destBound
      positive bounded (below.trans inv.2.2.2) below)

theorem returned_read_below (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (start length : Nat) (platform : 64 ≤ System.Platform.numBits)
    (inv : Invariant r pre tail) (countBound : r.x1.toNat < 2 ^ 64)
    (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (below : start + length ≤ r.x11.toNat) :
    (NativeSourceDynamicLoopReturn.returned n cost r pre tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have good := NativeSourceDynamicLoopGeometry.good_from_bounds n r countBound remaining endpoint
  unfold NativeSourceDynamicLoopReturn.returned NativeSourceDynamicLoopReturn.exited NativeSourceDynamicLoopReturn.tested
  rw [NativeSourceDynamicExit.memory, NativeSourceDynamicHeader.memory]
  exact iterate_read_below n cost r pre tail start length platform inv good positive bounded below

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopSourceFrame
