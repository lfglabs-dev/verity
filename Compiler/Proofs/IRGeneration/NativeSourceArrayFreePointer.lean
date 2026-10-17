import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocationDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayFreePointer
open EvmYul EVM EVM.Proof

def pushed (pre : EVM.State) :=
  (stepPre 3 pre).replaceStackAndIncrPC (UInt256.ofNat 64 :: pre.stack) 2

theorem push_step (fuel : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre = .ok (pushed pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode273]; rfl
  rw [decoded]
  rfl

theorem load_step (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 275)
    (stack : pre.stack = UInt256.ofNat 64 :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok (NativeSourceLoadStep.loaded 3 pre (UInt256.ofNat 64) tail) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode275]; rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel 3 pre _ tail stack

theorem swap_step (fuel : Nat) (pre : EVM.State) (pointer n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 276)
    (stack : pre.stack = pointer :: n :: x :: array :: tail) :
    EVM.step (fuel + 1) 3 (some (decodeAt pre)) pre =
      .ok ((stepPre 3 pre).replaceStackAndIncrPC (array :: n :: x :: pointer :: tail)) := by
  have decoded : decodeAt pre = (.SWAP3, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode276]; rfl
  rw [decoded]
  change EvmYul.swap 3 (stepPre 3 pre) = _
  unfold EvmYul.swap
  simp only [stepPre, stack]
  rfl

theorem load_frame (pre : EVM.State) (tail : Stack UInt256) :
    (NativeSourceLoadStep.loaded 3 pre (UInt256.ofNat 64) tail).stack =
      pre.toMachineState.lookupMemory (UInt256.ofNat 64) :: tail ∧
    (NativeSourceLoadStep.loaded 3 pre (UInt256.ofNat 64) tail).memory = pre.memory ∧
    (NativeSourceLoadStep.loaded 3 pre (UInt256.ofNat 64) tail).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeSourceArrayFreePointer
