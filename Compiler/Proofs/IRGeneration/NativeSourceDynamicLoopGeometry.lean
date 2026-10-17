import Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopInduction

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopGeometry
open EvmYul NativeSourceDynamicLoopInduction

theorem next_index (r : Registers) (bounded : r.x0.toNat + 1 < 2 ^ 256) :
    r.next.x0.toNat = r.x0.toNat + 1 := by
  exact NativeSourceFieldGeometry.offset_toNat r.x0 1 (by decide) bounded

theorem good_from_bounds (n : Nat) (r : Registers)
    (countBound : r.x1.toNat < 2 ^ 64)
    (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) : Good n r := by
  induction n generalizing r with
  | zero => trivial
  | succ n ih =>
    have index := next_index r (by omega)
    have dest := next_endpoint r (by omega)
    refine ⟨?_, ?_, ?_⟩
    · change r.x0.toNat < r.x1.toNat
      omega
    · omega
    · apply ih r.next countBound
      · rw [index]
        change r.x0.toNat + 1 + n ≤ r.x1.toNat
        omega
      · rw [dest]
        omega

theorem advance_count (n : Nat) (r : Registers) : (advance n r).x1 = r.x1 := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => exact ih r.next

theorem advance_values (n : Nat) (r : Registers)
    (indexBound : r.x0.toNat + n < 2 ^ 256)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    (advance n r).x0.toNat = r.x0.toNat + n ∧
      (advance n r).x11.toNat = r.x11.toNat + 128 * n := by
  induction n generalizing r with
  | zero => simp only [advance, Nat.mul_zero, Nat.add_zero, and_self]
  | succ n ih =>
    have index := next_index r (by omega)
    have dest := next_endpoint r (by omega)
    have ib : r.next.x0.toNat + n < 2 ^ 256 := by rw [index]; omega
    have eb : r.next.x11.toNat + 128 * n < 2 ^ 64 := by rw [dest]; omega
    have values := ih r.next ib eb
    rw [index, dest] at values
    change (advance n r.next).x0.toNat = _ ∧ (advance n r.next).x11.toNat = _
    omega

theorem terminal (n : Nat) (r : Registers)
    (countBound : r.x1.toNat < 2 ^ 64)
    (remaining : r.x0.toNat + n = r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    ¬(advance n r).x0 < (advance n r).x1 := by
  have values := advance_values n r (by omega) endpoint
  rw [advance_count]
  change ¬(advance n r).x0.toNat < r.x1.toNat
  omega

theorem execute_from_bounds (n fuel cost : Nat) (r : Registers) (pre : EVM.State) (tail : Stack UInt256)
    (platform : 64 ≤ System.Platform.numBits) (inv : Invariant r pre tail)
    (countBound : r.x1.toNat < 2 ^ 64)
    (remaining : r.x0.toNat + n ≤ r.x1.toNat)
    (endpoint : r.x11.toNat + 128 * n < 2 ^ 64) :
    NativeSourcePreludeDecoded.run fuel cost (62 * n) pre = .ok (iterate n cost r pre tail) := by
  exact NativeSourceDynamicLoopInduction.execute n fuel cost r pre tail platform inv
    (good_from_bounds n r countBound remaining endpoint)

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopGeometry
