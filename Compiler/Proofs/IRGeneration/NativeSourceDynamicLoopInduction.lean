import Compiler.Proofs.IRGeneration.NativeSourceDynamicIteration

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopInduction
open EvmYul EVM.Proof NativeSourcePreludeDecoded

structure Registers where
  x0 : UInt256
  x1 : UInt256
  x2 : UInt256
  x3 : UInt256
  x4 : UInt256
  x5 : UInt256
  x6 : UInt256
  x7 : UInt256
  x8 : UInt256
  x9 : UInt256
  x10 : UInt256
  x11 : UInt256
  x12 : UInt256
  x13 : UInt256
  x14 : UInt256
  x15 : UInt256

def Registers.stack (r : Registers) (tail : Stack UInt256) : Stack UInt256 :=
  r.x0 :: r.x1 :: r.x2 :: r.x3 :: r.x4 :: r.x5 :: r.x6 :: r.x7 :: r.x8 :: r.x9 :: r.x10 :: r.x11 :: r.x12 :: r.x13 :: r.x14 :: r.x15 :: tail

def Registers.next (r : Registers) : Registers :=
  { r with x0 := r.x0 + UInt256.ofNat 1, x2 := r.x2 + UInt256.ofNat 32, x11 := r.x11 + UInt256.ofNat 128 }

def Registers.step (r : Registers) (cost : Nat) (pre : EVM.State) (tail : Stack UInt256) :=
  NativeSourceDynamicIteration.returned cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail

def Good : Nat → Registers → Prop
  | 0, _ => True
  | n + 1, r => r.x0 < r.x1 ∧ r.x11.toNat + 128 < 2 ^ 64 ∧ Good n r.next

def Invariant (r : Registers) (pre : EVM.State) (tail : Stack UInt256) : Prop :=
  pre.executionEnv.code = NativeSourceAbiWrite.code ∧ pre.pc = UInt256.ofNat 551 ∧
    pre.stack = r.stack tail ∧ r.x11.toNat ≤ pre.memory.size

def iterate : Nat → Nat → Registers → EVM.State → Stack UInt256 → EVM.State
  | 0, _, _, pre, _ => pre
  | n + 1, cost, r, pre, tail => iterate n cost r.next (r.step cost pre tail) tail

def advance : Nat → Registers → Registers
  | 0, r => r
  | n + 1, r => advance n r.next

theorem next_endpoint (r : Registers) (bounded : r.x11.toNat + 128 < 2 ^ 64) :
    r.next.x11.toNat = r.x11.toNat + 128 := by
  exact NativeSourceFieldGeometry.offset_toNat r.x11 128 (by decide) (by omega)

theorem step_invariant (cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (bounded : r.x11.toNat + 128 < 2 ^ 64) :
    Invariant r.next (r.step cost pre tail) tail := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (NativeSourceDynamicIteration.code cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail).trans inv.1
  · exact NativeSourceDynamicIteration.header_pc cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail
  · exact NativeSourceDynamicIteration.output_stack cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail
  · rw [next_endpoint r bounded]
    exact NativeSourceDynamicIteration.endpoint_inside cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail platform (by omega)

theorem invariant_iterate (n cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail) (good : Good n r) :
    Invariant (advance n r) (iterate n cost r pre tail) tail := by
  induction n generalizing r pre with
  | zero => exact inv
  | succ n ih =>
    exact ih r.next (r.step cost pre tail) (step_invariant cost r pre tail platform inv good.2.1) good.2.2

theorem execute (n fuel cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail) (good : Good n r) :
    run fuel cost (62 * n) pre = .ok (iterate n cost r pre tail) := by
  induction n generalizing r pre with
  | zero => rfl
  | succ n ih =>
    have step := NativeSourceDynamicIteration.execute fuel cost pre r.x0 r.x1 r.x2 r.x3 r.x4 r.x5 r.x6 r.x7 r.x8 r.x9 r.x10 r.x11 r.x12 r.x13 r.x14 r.x15 tail
      inv.1 inv.2.1 inv.2.2.1 good.1
    have rest := ih r.next (r.step cost pre tail)
      (step_invariant cost r pre tail platform inv good.2.1) good.2.2
    have combined := NativeSourceSizedPacking.compose fuel cost 62 (62 * n) pre _ _ step rest
    simpa only [Nat.mul_succ, Nat.add_comm, iterate] using combined

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopInduction
