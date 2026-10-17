import Compiler.Proofs.IRGeneration.NativeSourceMarketCalldata
import Compiler.Proofs.IRGeneration.NativeSourcePackingCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressDecoderLoad
open EvmYul EVM.Proof CapturedMappingHelper
open Compiler.Proofs.YulGeneration.Backends

theorem decode945 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 945) = some (.CALLDATALOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 945 = some 53 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 945).toNat = 945 by decide, byte]
  decide

theorem checked_load (pre after : EVM.State) (address : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: tail) (success : checkedSteps 1 pre = .ok after) :
    after.stack = pre.toState.calldataload address :: tail ∧ after.toState = pre.toState ∧
      after.pc = UInt256.ofNat 946 ∧ after.memory = pre.memory := by
  obtain ⟨next, step, rest⟩ := checkedSteps_success 0 pre after success
  have decoded : decodeAt pre = (.CALLDATALOAD, none) := by
    unfold decodeAt
    rw [code, pc, decode945]
    rfl
  rw [decoded] at step
  have equal : next = after := Except.ok.inj rest
  subst next
  obtain ⟨out, world, atPC, memory⟩ := checked_calldataload_shape pre after address tail stack step
  refine ⟨out, world, ?_, memory⟩
  rw [atPC, pc]
  rfl

theorem aligned_value (pre after : EVM.State) (selector : Nat) (args : List Nat)
    (index arg : Nat) (rest : List Nat) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = UInt256.ofNat (4 + 32 * index) :: tail)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector args)
    (present : args.drop index = arg :: rest) (bounded : 4 + 32 * index < 2 ^ 64)
    (success : checkedSteps 1 pre = .ok after) :
    after.stack = pre.toState.calldataload (UInt256.ofNat (4 + 32 * index)) :: tail ∧
      (after.stack.head!).toNat = arg % Compiler.Constants.evmModulus ∧
      after.toState = pre.toState ∧ after.pc = UInt256.ofNat 946 ∧ after.memory = pre.memory := by
  obtain ⟨out, world, atPC, memory⟩ := checked_load pre after _ tail code pc stack success
  refine ⟨out, ?_, world, atPC, memory⟩
  rw [out]
  exact NativeSourceAbiInputs.encoded_argument pre selector args index arg rest encoded present bounded

end Compiler.Proofs.IRGeneration.NativeSourceAddressDecoderLoad
