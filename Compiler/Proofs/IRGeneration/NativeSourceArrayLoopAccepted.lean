import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopPrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopAccepted
open EvmYul EVM EVM.Proof NativeSourceArrayCalldataGuard

def entered (pre : EVM.State) (a end_ c : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayLoopPrefix.s4 (decided pre a end_ (c :: tail)) a end_ c tail

theorem execute (fuel : Nat) (pre : EVM.State) (a end_ c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 312)
    (stack : pre.stack = a :: end_ :: c :: tail) (gas : 31 ≤ pre.gasAvailable.toNat)
    (depth : tail.length ≤ 1019) (bound : pre.executionEnv.calldata.size < UInt256.size)
    (inside : end_.toNat ≤ pre.executionEnv.calldata.size) :
    EVM.X (fuel + 10) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (entered pre a end_ c tail) := by
  have charged := gas_exact pre a end_ (c :: tail) (by omega)
  have accepted := NativeSourceArrayCalldataBounds.accepted_pc pre a end_ (c :: tail) pc bound inside
  have frame := NativeSourceArrayCalldataOutcome.frame pre a end_ (c :: tail)
  rw [NativeSourceArrayCalldataGuard.execute (fuel + 4) pre a end_ (c :: tail) code pc stack
    (by omega) (by simp only [List.length_cons]; omega)]
  exact NativeSourceArrayLoopPrefix.execute fuel _ (decided pre a end_ (c :: tail)) a end_ c tail
    (by rw [frame.1]; exact code) accepted frame.2 (by omega) (by omega)

theorem output (pre : EVM.State) (a end_ c : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 312) (gas : 31 ≤ pre.gasAvailable.toNat)
    (bound : pre.executionEnv.calldata.size < UInt256.size)
    (inside : end_.toNat ≤ pre.executionEnv.calldata.size) :
    (entered pre a end_ c tail).pc = UInt256.ofNat 324 ∧
    (entered pre a end_ c tail).gasAvailable.toNat = pre.gasAvailable.toNat - 31 ∧
    (entered pre a end_ c tail).stack = c :: end_ :: (UInt256.ofNat 36 + a) :: tail := by
  have charged := gas_exact pre a end_ (c :: tail) (by omega)
  have accepted := NativeSourceArrayCalldataBounds.accepted_pc pre a end_ (c :: tail) pc bound inside
  have atPC := (NativeSourceArrayLoopPrefix.pcs (decided pre a end_ (c :: tail)) a end_ c tail accepted).2.2.2
  have finalGas := (NativeSourceArrayLoopPrefix.gas_chain (decided pre a end_ (c :: tail)) a end_ c tail (by omega)).2.2.2
  refine ⟨atPC, ?_, rfl⟩
  change (NativeSourceArrayLoopPrefix.s4 (decided pre a end_ (c :: tail)) a end_ c tail).gasAvailable.toNat = _
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopAccepted
