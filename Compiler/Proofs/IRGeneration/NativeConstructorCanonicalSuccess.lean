import Compiler.Proofs.IRGeneration.NativeConstructorAccountEffects
import Compiler.Proofs.IRGeneration.NativeConstructorCompletionGuard
import Compiler.Proofs.IRGeneration.NativeConstructorVacancy

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode
open Verity.Core.Model.Create2Runtime

/-- Native constructor success is precisely the canonical combined gas/runtime
predicate, rather than an assumed or independently chosen success flag. -/
theorem lambda_result_canonical_success (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result)
    (vacant : let target := nativeCreate2Target sender salt (initcode payload)
      (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0) :
    result.2.2.2.2.2.1 = (runtimeAccepted payload &&
      decide (prefixCost payload.size + Verity.Core.Model.Create2Callee.depositCost payload ≤ gas.toNat)) := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    have insufficient : ¬prefixCost payload.size + Verity.Core.Model.Create2Callee.depositCost payload ≤ gas.toNat := by omega
    simp only [insufficient, decide_false, Bool.and_false]
  · simp only [if_neg low] at completed
    cases completed
    have noCollision := constructor_vacancy_guard accounts
      (nativeCreate2Target sender salt (initcode payload)) vacant
    dsimp only
    have collisionEq : (match accounts.get? (nativeCreate2Target sender salt (initcode payload)) with
        | some account => decide (account.code ≠ ByteArray.empty ∨ account.nonce ≠ UInt256.ofNat 0)
        | none => false) = false := by
      cases found : accounts.get? (nativeCreate2Target sender salt (initcode payload)) with
      | none => rfl
      | some account =>
        rw [found] at noCollision
        exact noCollision
    simp only [Bool.decide_or, Bool.decide_coe, Pure.pure, Id.run]
    simp only [Bool.decide_or] at collisionEq
    trans !(false || (decide ((UInt256.ofNat (gas.toNat - prefixCost payload.size)).toNat <
      GasConstants.Gcodedeposit * payload.size) || nativeRuntimeRejected payload))
    · apply congrArg Bool.not
      apply congrArg₂ Bool.or
      · exact collisionEq
      · unfold nativeRuntimeRejected
        by_cases large : payload.size > 24576 <;> simp only [large, decide_true, decide_false] <;> rfl
    simp only [Bool.false_or]
    have guard := constructor_completion_guard payload gas (Nat.le_of_not_gt low)
    rw [guard, Bool.not_not]
    rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
