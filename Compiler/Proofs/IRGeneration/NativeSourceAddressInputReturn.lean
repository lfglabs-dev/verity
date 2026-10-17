import Compiler.Proofs.IRGeneration.NativeSourceAddressHelper

namespace Compiler.Proofs.IRGeneration.NativeSourceAddressInputReturn
open EvmYul EVM.Proof NativeSourcePreludeDecoded
open Compiler.Proofs.YulGeneration.Backends

def loaded (cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) : EVM.State :=
  (stepPre cost pre).replaceStackAndIncrPC (pre.toState.calldataload address :: ret :: tail)
abbrev result (cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressHelper.result cost (loaded cost pre address ret tail)
    (pre.toState.calldataload address) ret tail
abbrev rejected (cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :=
  NativeSourceAddressHelper.branch cost (loaded cost pre address ret tail)
    (pre.toState.calldataload address) ret tail

theorem load_step (fuel cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (loaded cost pre address ret tail) := by
  have decoded : decodeAt pre = (.CALLDATALOAD, none) := by
    unfold decodeAt
    rw [code, pc, NativeSourceAddressDecoderLoad.decode945]; rfl
  rw [decoded]
  change EvmYul.step (τ := .EVM) .CALLDATALOAD none (stepPre cost pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  rfl

theorem loaded_pc (cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 945) :
    (loaded cost pre address ret tail).pc = UInt256.ofNat 946 := by
  change pre.pc + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem loaded_code (cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256) :
    (loaded cost pre address ret tail).executionEnv.code = pre.executionEnv.code := by rfl

theorem load_run (fuel cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail) :
    run fuel cost 1 pre = .ok (loaded cost pre address ret tail) := by
  rw [run, load_step fuel cost pre address ret tail code pc stack]
  rfl

theorem execute_return (fuel cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail)
    (canonical : (pre.toState.calldataload address).toNat < 2 ^ 160) :
    run fuel cost 14 pre = .ok (result cost pre address ret tail) := by
  exact NativeSourceSizedPacking.compose fuel cost 1 13 pre _ _
    (load_run fuel cost pre address ret tail code pc stack)
    (NativeSourceAddressHelper.execute_return fuel cost (loaded cost pre address ret tail)
      (pre.toState.calldataload address) ret tail ((loaded_code cost pre address ret tail).trans code)
      (loaded_pc cost pre address ret tail pc) (by rfl) canonical)

theorem invalid_execute (fuel cost : Nat) (pre : EVM.State) (address ret : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 945)
    (stack : pre.stack = address :: ret :: tail)
    (invalid : ¬(pre.toState.calldataload address).toNat < 2 ^ 160) :
    run fuel cost 13 pre = .ok (rejected cost pre address ret tail) ∧
      (rejected cost pre address ret tail).pc = UInt256.ofNat 91 := by
  constructor
  · exact NativeSourceSizedPacking.compose fuel cost 1 12 pre _ _
      (load_run fuel cost pre address ret tail code pc stack)
      (NativeSourceAddressHelper.execute_branch fuel cost (loaded cost pre address ret tail)
        (pre.toState.calldataload address) ret tail ((loaded_code cost pre address ret tail).trans code)
        (loaded_pc cost pre address ret tail pc) (by rfl))
  · exact (NativeSourceAddressHelper.invalid_branch cost (loaded cost pre address ret tail)
      (pre.toState.calldataload address) ret tail (loaded_pc cost pre address ret tail pc) invalid).1

theorem original_value (cost : Nat) (pre : EVM.State) (selector : Nat) (args : List Nat)
    (index arg : Nat) (rest : List Nat) (ret : UInt256) (tail : Stack UInt256)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector args)
    (present : args.drop index = arg :: rest) (bounded : 4 + 32 * index < 2 ^ 64) :
    ((result cost pre (UInt256.ofNat (4 + 32 * index)) ret tail).stack.head!).toNat =
      arg % Compiler.Constants.evmModulus := by
  have frame := (NativeSourceAddressHelper.result_frame cost (loaded cost pre (UInt256.ofNat (4 + 32 * index)) ret tail)
    (pre.toState.calldataload (UInt256.ofNat (4 + 32 * index))) ret tail).1
  rw [frame]
  exact NativeSourceAbiInputs.encoded_argument pre selector args index arg rest encoded present bounded

end Compiler.Proofs.IRGeneration.NativeSourceAddressInputReturn
