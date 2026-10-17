import Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataBounds
open EvmYul EVM EVM.Proof NativeSourceArrayCalldataGuard

theorem size_value (pre : EVM.State) (bound : pre.executionEnv.calldata.size < UInt256.size) :
    (size pre).toNat = pre.executionEnv.calldata.size := by
  change pre.executionEnv.calldata.size % UInt256.size = _
  exact Nat.mod_eq_of_lt bound

theorem flag_zero (pre : EVM.State) (end_ : UInt256)
    (bound : pre.executionEnv.calldata.size < UInt256.size)
    (inside : end_.toNat ≤ pre.executionEnv.calldata.size) : flag pre end_ = UInt256.ofNat 0 := by
  have exactSize := size_value pre bound
  have ordered : ¬end_ > size pre := by
    change ¬end_.val > (size pre).val
    change ¬end_.toNat > (size pre).toNat
    omega
  simp [flag, UInt256.gt, UInt256.fromBool, ordered]

theorem flag_one (pre : EVM.State) (end_ : UInt256)
    (bound : pre.executionEnv.calldata.size < UInt256.size)
    (outside : pre.executionEnv.calldata.size < end_.toNat) : flag pre end_ = UInt256.ofNat 1 := by
  have exactSize := size_value pre bound
  have ordered : end_ > size pre := by
    change end_.val > (size pre).val
    change end_.toNat > (size pre).toNat
    omega
  simp [flag, UInt256.gt, UInt256.fromBool, ordered]

theorem destinations (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 312) :
    (decided pre a end_ tail).pc = if flag pre end_ != ⟨0⟩ then UInt256.ofNat 91 else UInt256.ofNat 319 := by
  exact NativeSourceArrayCalldataBranch.destinations (s4 pre a end_ tail) (flag pre end_) (a :: end_ :: tail)
    (pcs pre a end_ tail pc).2.2.2

theorem accepted_pc (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 312) (bound : pre.executionEnv.calldata.size < UInt256.size)
    (inside : end_.toNat ≤ pre.executionEnv.calldata.size) :
    (decided pre a end_ tail).pc = UInt256.ofNat 319 := by
  rw [destinations pre a end_ tail pc, flag_zero pre end_ bound inside]
  rfl

theorem rejected_pc (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 312) (bound : pre.executionEnv.calldata.size < UInt256.size)
    (outside : pre.executionEnv.calldata.size < end_.toNat) :
    (decided pre a end_ tail).pc = UInt256.ofNat 91 := by
  rw [destinations pre a end_ tail pc, flag_one pre end_ bound outside]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataBounds
