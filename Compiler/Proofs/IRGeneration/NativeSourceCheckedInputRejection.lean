import Compiler.Proofs.IRGeneration.NativeSourceCheckedGuard
import Compiler.Proofs.IRGeneration.NativeSourceAddressInputReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedInputRejection
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups NativeSourceAddressInputReturn

theorem load_check (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .CALLDATALOAD pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .CALLDATALOAD = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 1 by omega, show ¬pre.stack.length - 1 + 1 > 1024 by omega]

theorem continue_load (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) (gas : 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 2) jumps pre = EVM.X (fuel + 1) jumps (loaded 3 pre address ret tail) := by
  have decoded : decodeAt pre = (.CALLDATALOAD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceAddressDecoderLoad.decode945]; rfl
  have check := load_check jumps pre (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas)
    (by simp only [stack, List.length_cons]; omega)
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  have step := load_step fuel 3 pre address ret tail code pc stack
  rw [decoded] at step
  exact X_succ_of_continue decoded check step rfl

theorem reject_exact (fuel : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) (invalid : ¬(pre.toState.calldataload address).toNat < 2 ^ 160)
    (gas : 52 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1019) :
    EVM.X (fuel + 18) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 52)) ByteArray.empty) := by
  have charged : (loaded 3 pre address ret tail).gasAvailable.toNat = pre.gasAvailable.toNat - 3 :=
    NativeSourceCheckedRejection.gas_sub _ 3 (by decide) (by omega)
  rw [continue_load (fuel + 16) _ pre address ret tail code pc stack (by omega) depth]
  rw [NativeSourceCheckedGuard.reject_exact fuel _ (pre.toState.calldataload address) ret tail
    ((loaded_code 3 pre address ret tail).trans code) (loaded_pc 3 pre address ret tail pc)
    rfl invalid (by omega) depth, charged]
  congr 3

end Compiler.Proofs.IRGeneration.NativeSourceCheckedInputRejection
