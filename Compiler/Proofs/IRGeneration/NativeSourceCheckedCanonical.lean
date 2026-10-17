import Compiler.Proofs.IRGeneration.NativeSourceCheckedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedCanonical
open EvmYul EVM EVM.Proof NativeSourceAddressGuardExecution

def afterGuard (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressBranch.returned 8
    (NativeSourceCheckedReturn.fallthrough (NativeSourceAddressBranch.pushed 3 (s10 3 pre word ret tail))
      (ret :: word :: tail)) ret word tail

theorem guard_return (fuel : Nat) (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 946)
    (stack : pre.stack = word :: ret :: tail) (canonical : word.toNat < 2 ^ 160)
    (gas : 51 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (destination : ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) :
    EVM.X (fuel + 14) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (afterGuard pre word ret tail) := by
  have charged := (NativeSourceCheckedGuard.gas_chain pre word ret tail (by omega)).2.2.2.2.2.2.2.2.2
  have zero := (NativeSourceAddressCanonicality.difference_zero_iff word).mpr canonical
  have codeAfter := (NativeSourceAddressHelper.guard_code 3 pre word ret tail).trans code
  rw [NativeSourceCheckedGuard.execute (fuel + 3) _ pre word ret tail code pc stack (by omega) depth]
  exact NativeSourceCheckedReturn.execute_branch_return fuel _ ret word tail codeAfter
    (NativeSourceAddressHelper.guard_pc 3 pre word ret tail pc)
    (by rw [output_stack, zero]) (by omega) (by omega) destination

theorem guard_gas (pre : EVM.State) (word ret : UInt256) (tail : Stack UInt256)
    (gas : 51 ≤ pre.gasAvailable.toNat) :
    (afterGuard pre word ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 51 := by
  have g0 := (NativeSourceCheckedGuard.gas_chain pre word ret tail (by omega)).2.2.2.2.2.2.2.2.2
  have g1 : (NativeSourceAddressBranch.pushed 3 (s10 3 pre word ret tail)).gasAvailable.toNat =
      (s10 3 pre word ret tail).gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have g2 : (NativeSourceCheckedReturn.fallthrough (NativeSourceAddressBranch.pushed 3 (s10 3 pre word ret tail))
      (ret :: word :: tail)).gasAvailable.toNat =
      (NativeSourceAddressBranch.pushed 3 (s10 3 pre word ret tail)).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  have g3 : (afterGuard pre word ret tail).gasAvailable.toNat =
      (NativeSourceCheckedReturn.fallthrough (NativeSourceAddressBranch.pushed 3 (s10 3 pre word ret tail))
      (ret :: word :: tail)).gasAvailable.toNat - 8 :=
    NativeSourceCheckedRejection.gas_sub _ 8 (by decide) (by omega)
  omega

def result (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :=
  afterGuard (NativeSourceAddressInputReturn.loaded 3 pre address ret tail) (pre.toState.calldataload address) ret tail

theorem input_return (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) (canonical : (pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 54 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019)
    (destination : ret ∈ EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) :
    EVM.X (fuel + 15) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (result pre address ret tail) := by
  have charged : (NativeSourceAddressInputReturn.loaded 3 pre address ret tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - 3 := NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  rw [NativeSourceCheckedInputRejection.continue_load (fuel + 13) _ pre address ret tail code pc stack (by omega) depth]
  exact guard_return fuel _ _ ret tail ((NativeSourceAddressInputReturn.loaded_code 3 pre address ret tail).trans code)
    (NativeSourceAddressInputReturn.loaded_pc 3 pre address ret tail pc) rfl canonical (by omega) depth destination

theorem input_gas (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (gas : 54 ≤ pre.gasAvailable.toNat) :
    (result pre address ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 54 := by
  have charged : (NativeSourceAddressInputReturn.loaded 3 pre address ret tail).gasAvailable.toNat =
      pre.gasAvailable.toNat - 3 := NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  have guard := guard_gas (NativeSourceAddressInputReturn.loaded 3 pre address ret tail)
    (pre.toState.calldataload address) ret tail (by omega)
  change (result pre address ret tail).gasAvailable.toNat = _ at guard
  omega

theorem result_frame (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (result pre address ret tail).stack = pre.toState.calldataload address :: tail ∧
      (result pre address ret tail).pc = ret := by
  exact ⟨rfl, rfl⟩

end Compiler.Proofs.IRGeneration.NativeSourceCheckedCanonical
