import Verity.Core.Model.DenoteCreate2
import Compiler.SolidityImport.Transactions

namespace SolidityImportSmoke.DeploymentWorldChecks
open Verity.Core
open Compiler.CompilationModel.DenoteCreate2

private def noHash : ByteHash := fun _ => 0
private def creator : Address := Address.ofNat 1
private def maxNonceWorld : Verity.ContractState :=
  Verity.defaultState.writeAccount creator { nonce := ⟨2^64 - 1, by decide⟩ }

theorem nonce_limit_returns_zero_without_increment :
    denoteCreate2 noHash maxNonceWorld { creator, childGas := 1000 } 0 [] =
      .ok { control := .zero .nonceLimit, world := maxNonceWorld, childGasLeft := 1000 } := rfl

theorem insufficient_balance_does_not_increment :
    denoteCreate2 noHash Verity.defaultState { creator, value := 1, childGas := 1000 } 0 [] =
      .ok { control := .zero .insufficientBalance, world := Verity.defaultState, childGasLeft := 1000 } := rfl

theorem depth_limit_does_not_increment :
    denoteCreate2 noHash Verity.defaultState { creator, childGas := 1000, depth := 1024 } 0 [] =
      .ok { control := .zero .depth, world := Verity.defaultState, childGasLeft := 1000 } := rfl

theorem unsupported_initcode_is_instrument_error :
    denoteCreate2 noHash Verity.defaultState { creator, childGas := 1000 } 0 [] =
      .error "CREATE2 initcode gas semantics are unsupported for these bytes" := rfl

theorem metadata_survives_storage_write (world : Verity.ContractState) (slot : Nat) (value : Uint256) :
    (world.writeSlot slot value).accountWorld = world.accountWorld :=
  Verity.ContractState.accountWorld_writeSlot world slot value

end SolidityImportSmoke.DeploymentWorldChecks
