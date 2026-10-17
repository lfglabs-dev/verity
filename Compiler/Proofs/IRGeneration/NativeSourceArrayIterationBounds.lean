import Compiler.Proofs.IRGeneration.NativeSourceArrayIterationGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayIterationBounds
open EvmYul EVM EVM.Proof NativeSourceArrayIterationGuard

theorem flag_one (end_ cursor : UInt256) (inside : cursor.toNat < end_.toNat) :
    flag end_ cursor = UInt256.ofNat 1 := by
  have ordered : cursor < end_ := by
    change cursor.val < end_.val
    change cursor.toNat < end_.toNat
    exact inside
  simp [flag, UInt256.lt, UInt256.fromBool, ordered]

theorem flag_zero (end_ cursor : UInt256) (finished : end_.toNat ≤ cursor.toNat) :
    flag end_ cursor = UInt256.ofNat 0 := by
  have ordered : ¬cursor < end_ := by
    change ¬cursor.val < end_.val
    change ¬cursor.toNat < end_.toNat
    omega
  simp [flag, UInt256.lt, UInt256.fromBool, ordered]

theorem destinations (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 324) :
    (decided pre a end_ cursor tail).pc =
      if flag end_ cursor != ⟨0⟩ then UInt256.ofNat 806 else UInt256.ofNat 331 := by
  exact NativeSourceArrayIterationBranch.destinations (s4 pre a end_ cursor tail) (flag end_ cursor)
    (a :: end_ :: cursor :: tail) (pcs pre a end_ cursor tail pc).2.2.2

theorem iterate_pc (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 324) (inside : cursor.toNat < end_.toNat) :
    (decided pre a end_ cursor tail).pc = UInt256.ofNat 806 := by
  rw [destinations pre a end_ cursor tail pc, flag_one end_ cursor inside]
  rfl

theorem finished_pc (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 324) (finished : end_.toNat ≤ cursor.toNat) :
    (decided pre a end_ cursor tail).pc = UInt256.ofNat 331 := by
  rw [destinations pre a end_ cursor tail pc, flag_zero end_ cursor finished]
  rfl

theorem frame (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256) :
    (decided pre a end_ cursor tail).stack = a :: end_ :: cursor :: tail ∧
    (decided pre a end_ cursor tail).executionEnv = pre.executionEnv ∧
    (decided pre a end_ cursor tail).memory = pre.memory ∧
    (decided pre a end_ cursor tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeSourceArrayIterationBounds
