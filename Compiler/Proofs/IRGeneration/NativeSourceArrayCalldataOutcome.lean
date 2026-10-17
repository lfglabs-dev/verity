import Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataOutcome
open EvmYul EVM EVM.Proof NativeSourceArrayCalldataGuard

theorem frame (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256) :
    (decided pre a end_ tail).executionEnv = pre.executionEnv ∧
    (decided pre a end_ tail).stack = a :: end_ :: tail := by
  constructor <;> rfl

theorem reject_exact (fuel : Nat) (pre : EVM.State) (a end_ : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 312)
    (stack : pre.stack = a :: end_ :: tail) (gas : 27 ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1020) (bound : pre.executionEnv.calldata.size < UInt256.size)
    (outside : pre.executionEnv.calldata.size < end_.toNat) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 27)) ByteArray.empty) := by
  have charged := gas_exact pre a end_ tail (by omega)
  have rejected := NativeSourceArrayCalldataBounds.rejected_pc pre a end_ tail pc bound outside
  have env := (frame pre a end_ tail).1
  have stk := (frame pre a end_ tail).2
  rw [NativeSourceArrayCalldataGuard.execute (fuel + 4) pre a end_ tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedRejection.execute_exact fuel _ (decided pre a end_ tail)
    (by rw [env]; exact code) rejected (by omega)
    (by rw [stk]; simp only [List.length_cons]; omega)]
  rw [charged, Nat.sub_sub]

end Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataOutcome
