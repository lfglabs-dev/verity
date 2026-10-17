import Compiler.Proofs.IRGeneration.NativeConstructorRuntimeGuard
import Verity.Core.Model.Create2Callee

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode
open Verity.Core.Model.Create2Runtime

/-- Exact native post-constructor gas/runtime rejection, with collision handled
separately by the actual nonce/code guard. -/
theorem constructor_completion_guard (payload : ByteArray) (gas : UInt256)
    (funded : prefixCost payload.size ≤ gas.toNat) :
    (decide ((UInt256.ofNat (gas.toNat - prefixCost payload.size)).toNat <
        GasConstants.Gcodedeposit * payload.size) || nativeRuntimeRejected payload) =
      !(runtimeAccepted payload && decide (prefixCost payload.size + 200 * payload.size ≤ gas.toNat)) := by
  rw [runtime_guard, constructor_remaining_nat]
  change (decide (gas.toNat - prefixCost payload.size < 200 * payload.size) ||
    !runtimeAccepted payload) = _
  by_cases enough : prefixCost payload.size + 200 * payload.size ≤ gas.toNat
  · have deposit : ¬gas.toNat - prefixCost payload.size < 200 * payload.size := by omega
    simp only [deposit, decide_false, Bool.false_or, enough, decide_true, Bool.and_true]
  · have deposit : gas.toNat - prefixCost payload.size < 200 * payload.size := by omega
    simp only [deposit, decide_true, Bool.true_or, enough, decide_false, Bool.and_false, Bool.not_false]

/-- Native post-deposit natural gas is exactly the canonical combined debit. -/
theorem constructor_completion_gas (payload : ByteArray) (gas : UInt256) :
    (UInt256.ofNat (gas.toNat - prefixCost payload.size)).toNat -
        GasConstants.Gcodedeposit * payload.size =
      gas.toNat - (prefixCost payload.size + Verity.Core.Model.Create2Callee.depositCost payload) := by
  rw [constructor_remaining_nat]
  change gas.toNat - prefixCost payload.size - 200 * payload.size =
    gas.toNat - (prefixCost payload.size + 200 * payload.size)
  omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
