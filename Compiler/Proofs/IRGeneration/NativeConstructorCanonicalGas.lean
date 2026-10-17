import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalSuccess

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode
open Verity.Core.Model.Create2Callee

private theorem result_gas_choice (payload : ByteArray) (gas : UInt256) (rejected : Bool) :
    (UInt256.ofNat (if rejected then 0 else
      (UInt256.ofNat (gas.toNat - prefixCost payload.size)).toNat - GasConstants.Gcodedeposit * payload.size)).toNat =
    if !rejected then gas.toNat - (prefixCost payload.size + depositCost payload) else 0 := by
  cases rejected with
  | true => rfl
  | false =>
    change (UInt256.ofNat ((UInt256.ofNat (gas.toNat - prefixCost payload.size)).toNat -
      GasConstants.Gcodedeposit * payload.size)).toNat = _
    rw [constructor_completion_gas]
    change (gas.toNat - (prefixCost payload.size + depositCost payload)) % UInt256.size = _
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) gas.val.isLt)

/-- Native remaining gas is the full canonical debit on success and exactly
zero on any completed failure, including failed prefix execution. -/
theorem lambda_result_canonical_gas (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result) :
    result.2.2.2.1.toNat = if result.2.2.2.2.2.1 then
      gas.toNat - (prefixCost payload.size + depositCost payload) else 0 := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    rfl
  · simp only [if_neg low] at completed
    cases completed
    exact result_gas_choice payload gas _

/-- Status, runtime and gas of the completed native formula agree with the
canonical callee evaluation, for all funded and unfunded gas inputs. -/
theorem lambda_result_canonical_callee (payload : ByteArray)
    (bounded : 11 + payload.size < Verity.Core.Model.MidnightInitcode.modulus)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (vacant : let target := nativeCreate2Target sender salt (initcode payload)
      (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0) :
    execute payload gas.toNat = .ok
      { result := if result.2.2.2.2.2.1 then .returned payload true else .exceptional
        gasLeft := result.2.2.2.1.toNat } := by
  rw [execute_formula payload bounded gas.toNat,
    lambda_result_canonical_gas payload created accounts substate sender gas value salt result completed]
  have success := lambda_result_canonical_success payload created accounts substate sender gas value salt
    result completed vacant
  rw [success]
  split <;> rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
