import Compiler.Proofs.IRGeneration.NativeSourceCheckedCanonical

namespace Compiler.Proofs.IRGeneration.NativeSourceCanonicalFrames
open EvmYul EVM EVM.Proof

theorem return_world (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressBranch.returned 8 pre ret word tail).toState = pre.toState := by rfl

theorem return_memory (pre : EVM.State) (ret word : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressBranch.returned 8 pre ret word tail).memory = pre.memory := by rfl

theorem fallthrough_world (pre : EVM.State) (tail : Stack UInt256) :
    (NativeSourceCheckedReturn.fallthrough pre tail).toState = pre.toState := by rfl

theorem fallthrough_memory (pre : EVM.State) (tail : Stack UInt256) :
    (NativeSourceCheckedReturn.fallthrough pre tail).memory = pre.memory := by rfl

theorem push_world (pre : EVM.State) :
    (NativeSourceAddressBranch.pushed 3 pre).toState = pre.toState := by rfl

theorem push_memory (pre : EVM.State) :
    (NativeSourceAddressBranch.pushed 3 pre).memory = pre.memory := by rfl

theorem guard_world (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedCanonical.afterGuard pre word ret tail).toState = pre.toState := by
  unfold NativeSourceCheckedCanonical.afterGuard
  rw [return_world, fallthrough_world, push_world]
  exact NativeSourceAddressHelper.guard_world 3 pre word ret tail

theorem guard_memory (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedCanonical.afterGuard pre word ret tail).memory = pre.memory := by
  unfold NativeSourceCheckedCanonical.afterGuard
  rw [return_memory, fallthrough_memory, push_memory]
  exact NativeSourceAddressGuardExecution.memory 3 pre word ret tail

theorem load_world (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressInputReturn.loaded 3 pre address ret tail).toState = pre.toState := by rfl

theorem load_memory (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceAddressInputReturn.loaded 3 pre address ret tail).memory = pre.memory := by rfl

theorem input_world (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedCanonical.result pre address ret tail).toState = pre.toState := by
  unfold NativeSourceCheckedCanonical.result
  rw [guard_world, load_world]

theorem input_memory (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedCanonical.result pre address ret tail).memory = pre.memory := by
  unfold NativeSourceCheckedCanonical.result
  rw [guard_memory, load_memory]

end Compiler.Proofs.IRGeneration.NativeSourceCanonicalFrames
