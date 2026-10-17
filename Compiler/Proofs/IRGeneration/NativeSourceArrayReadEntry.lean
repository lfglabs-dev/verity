import Compiler.Proofs.IRGeneration.NativeSourceArrayCallJump

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayReadEntry
open EvmYul EVM EVM.Proof NativeSourceArrayCheckedPointer

def pointer (pre : EVM.State) := pre.toMachineState.lookupMemory (UInt256.ofNat 64)
def expansion (pre : EVM.State) := memoryExpansionCost (NativeSourceArrayFreePointer.pushed pre) .MLOAD

def prepared (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  (stepPre 3 (read pre)).replaceStackAndIncrPC (array :: n :: x :: pointer pre :: tail)

theorem read_frame (pre : EVM.State) :
    (read pre).stack = pointer pre :: pre.stack ∧ (read pre).memory = pre.memory ∧
    (read pre).toState = pre.toState := by
  exact ⟨rfl, rfl, rfl⟩

theorem read_pc (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 273) :
    (read pre).pc = UInt256.ofNat 276 := by
  change (pre.pc + UInt256.ofNat 2) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem budgets (pre : EVM.State) (gas : expansion pre + 41 ≤ pre.gasAvailable.toNat) :
    3 ≤ pre.gasAvailable.toNat ∧
    expansion pre + 3 ≤ (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat ∧
    35 ≤ (read pre).gasAvailable.toNat := by
  have pushed : (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have enough : memoryExpansionCost (NativeSourceArrayFreePointer.pushed pre) .MLOAD + 3 ≤
      (NativeSourceArrayFreePointer.pushed pre).gasAvailable.toNat := by change expansion pre + 3 ≤ _; omega
  have readGas := read_gas pre (by omega) enough
  change (read pre).gasAvailable.toNat = pre.gasAvailable.toNat - 6 - expansion pre at readGas
  omega

theorem execute (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (stack : pre.stack = n :: x :: array :: tail)
    (gas : expansion pre + 41 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 4) jumps pre = EVM.X (fuel + 1) jumps (prepared pre n x array tail) := by
  obtain ⟨initial, loadGas, readGas⟩ := budgets pre gas
  rw [read_execute (fuel + 1) jumps pre code pc initial loadGas (by simp only [stack, List.length_cons]; omega)]
  exact swap_continue fuel jumps (read pre) (pointer pre) n x array tail code (read_pc pre pc)
    (by rw [(read_frame pre).1, stack]) (by omega) (by omega)

theorem prepared_gas (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (gas : expansion pre + 41 ≤ pre.gasAvailable.toNat) :
    (prepared pre n x array tail).gasAvailable.toNat = pre.gasAvailable.toNat - 9 - expansion pre := by
  obtain ⟨initial, loadGas, readGas⟩ := budgets pre gas
  have charged := read_gas pre initial loadGas
  change (read pre).gasAvailable.toNat = pre.gasAvailable.toNat - 6 - expansion pre at charged
  have final : (prepared pre n x array tail).gasAvailable.toNat = (read pre).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  omega

theorem prepared_frame (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 273) :
    (prepared pre n x array tail).pc = UInt256.ofNat 277 ∧
    (prepared pre n x array tail).stack = array :: n :: x :: pointer pre :: tail ∧
    (prepared pre n x array tail).memory = pre.memory ∧
    (prepared pre n x array tail).toState = pre.toState := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (read pre).pc + UInt256.ofNat 1 = _
  rw [read_pc pre pc]; decide

def called (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :=
  NativeSourceArrayCallJump.called (prepared pre n x array tail) array n x (pointer pre) tail

theorem call_execute (fuel : Nat) (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 273)
    (stack : pre.stack = n :: x :: array :: tail)
    (gas : expansion pre + 41 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 13) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (called pre n x array tail) := by
  have charged := prepared_gas pre n x array tail gas
  have shape := prepared_frame pre n x array tail pc
  rw [execute (fuel + 9) _ pre n x array tail code pc stack gas depth]
  exact NativeSourceArrayCallJump.execute fuel _ array n x (pointer pre) tail code shape.1 shape.2.1 (by omega) depth

theorem call_gas (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256)
    (gas : expansion pre + 41 ≤ pre.gasAvailable.toNat) :
    (called pre n x array tail).gasAvailable.toNat = pre.gasAvailable.toNat - 41 - expansion pre := by
  have charged := prepared_gas pre n x array tail gas
  have final := NativeSourceArrayCallJump.gas_exact (prepared pre n x array tail) array n x (pointer pre) tail (by omega)
  change (called pre n x array tail).gasAvailable.toNat = _ at final
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayReadEntry
