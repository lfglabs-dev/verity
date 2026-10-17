import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalGas
import Compiler.Proofs.IRGeneration.NativeConstructorLambdaAdequacy

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode
open Verity.Core.Model.Create2Callee

/-- Exact address, bookkeeping and return bytes of every completed native
formula result, including constructor and deposit failures. -/
theorem lambda_result_bookkeeping (payload : ByteArray)
    (created : Std.TreeSet AccountAddress compare) (accounts : AccountMap .EVM)
    (substate : Substate) (sender : AccountAddress) (gas value : UInt256) (salt : ByteArray)
    (result : AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM ×
      UInt256 × Substate × Bool × ByteArray)
    (completed : lambdaConstructorResult payload created accounts substate sender gas value salt = .ok result) :
    let target := nativeCreate2Target sender salt (initcode payload)
    result.1 = target ∧ result.2.1 = created.insert target ∧
      result.2.2.2.2.1 = substate.addAccessedAccount target ∧ result.2.2.2.2.2.2 = ByteArray.empty := by
  unfold lambdaConstructorResult at completed
  by_cases low : gas.toNat < prefixCost payload.size
  · simp only [if_pos low] at completed
    cases completed
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [if_neg low] at completed
    cases completed
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Transport canonical callee status/runtime/gas through the actual pinned
Lambda. This theorem derives the native completed result rather than assuming
an independently selected child success or gas certificate. -/
theorem lambda_canonical_callee (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (blobs : List ByteArray) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks)
    (accounts original : AccountMap .EVM) (substate : Substate)
    (sender origin : AccountAddress) (gas price value depth : UInt256)
    (salt : ByteArray) (header : BlockHeader) (permission : Bool)
    (vacant : let target := nativeCreate2Target sender salt (initcode payload)
      (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    ∃ result, EVM.Lambda (fuel + 2) blobs created genesis blocks accounts original substate
      sender origin gas price value (initcode payload) depth (some salt) header permission = .ok result ∧
      execute payload gas.toNat = .ok
        { result := if result.2.2.2.2.2.1 then .returned payload true else .exceptional
          gasLeft := result.2.2.2.1.toNat } ∧
      result.2.2.2.2.2.2 = ByteArray.empty := by
  obtain ⟨result, completed⟩ := lambda_all_targets_completed payload bounded blobs created genesis blocks
    accounts original substate sender origin gas price value depth salt header permission fuel enough
  refine ⟨result, completed, ?_⟩
  rw [lambda_constructor payload bounded blobs created genesis blocks accounts original substate
    sender origin gas price value depth salt header permission vacant fuel enough] at completed
  have large : 49163 < modulus := by decide
  have nowrap : 11 + payload.size < modulus := by omega
  exact ⟨lambda_result_canonical_callee payload nowrap created accounts substate sender gas value salt
    result completed vacant,
    (lambda_result_bookkeeping payload created accounts substate sender gas value salt result completed).2.2.2⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
