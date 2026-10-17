import Compiler.Proofs.IRGeneration.NativeSourceAbiWrite
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeCalldata

namespace Compiler.Proofs.IRGeneration.NativeSourceAbiInputs
open EvmYul
open Compiler.Proofs.YulGeneration
open Compiler.Proofs.YulGeneration.Backends

/-- The original byte calldata, rather than supplied boundary values, determines
any present aligned ABI word. Reuse the native state bridge's encoding theorem. -/
theorem encoded_argument (machine : EVM.State) (selector : Nat) (args : List Nat)
    (index arg : Nat) (rest : List Nat)
    (encoded : machine.executionEnv.calldata = StateBridge.calldataToByteArray selector args)
    (present : args.drop index = arg :: rest) (bounded : 4 + 32 * index < 2 ^ 64) :
    (machine.toState.calldataload (UInt256.ofNat (4 + 32 * index))).toNat =
      arg % Compiler.Constants.evmModulus := by
  let tx : YulTransaction := { sender := 0, functionSelector := selector, args := args }
  have actual := Native.initialState_calldataload_aligned_arg_value
    (Inhabited.default : EvmYul.Yul.Ast.YulContract) tx (fun _ => 0) [] index arg rest present bounded
  change (uInt256OfByteArray ((StateBridge.calldataToByteArray selector args).readBytes
    (UInt256.ofNat (4 + 32 * index)).toNat 32)).toNat = _ at actual
  simpa only [EvmYul.State.calldataload, encoded, EvmYul.UInt256.size] using actual

/-- Original calldata offsets36/68 are exactly ABI argument words1/2. -/
theorem encoded_mapping_arguments (machine : EVM.State)
    (selector offset key value : Nat) (rest : List Nat)
    (encoded : machine.executionEnv.calldata = StateBridge.calldataToByteArray selector
      (offset :: key :: value :: rest)) :
    (machine.toState.calldataload (UInt256.ofNat 36)).toNat = key % Compiler.Constants.evmModulus ∧
      (machine.toState.calldataload (UInt256.ofNat 68)).toNat = value % Compiler.Constants.evmModulus := by
  exact ⟨encoded_argument machine selector _ 1 key _ encoded rfl (by decide),
    encoded_argument machine selector _ 2 value _ encoded rfl (by decide)⟩

end Compiler.Proofs.IRGeneration.NativeSourceAbiInputs
