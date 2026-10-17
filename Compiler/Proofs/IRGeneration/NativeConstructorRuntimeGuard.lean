import Verity.Core.Model.Create2Runtime
import Compiler.Proofs.IRGeneration.NativeConstructorXiResult

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

/-- The actual native runtime rejection guard, excluding collision and gas. -/
def nativeRuntimeRejected (payload : ByteArray) : Bool :=
  let large := payload.size > 24576
  decide large || (!decide large && decide (payload[0]? = some 0xef))

/-- Native size/0xef guards and the canonical runtime predicate agree,
including empty payloads. -/
theorem runtime_guard (payload : ByteArray) :
    nativeRuntimeRejected payload = !Verity.Core.Model.Create2Runtime.runtimeAccepted payload := by
  unfold nativeRuntimeRejected Verity.Core.Model.Create2Runtime.runtimeAccepted
  by_cases large : payload.size > 24576
  · simp only [large, decide_true, Bool.true_or, Nat.not_le.mpr large, decide_false,
      Bool.false_and, Bool.not_false]
  · have small : payload.size ≤ 24576 := Nat.le_of_not_gt large
    simp only [large, decide_false, Bool.not_false, Bool.true_and, Bool.false_or,
      small, decide_true, Bool.true_and]
    have optionEq : payload[0]? = payload.data[0]? := by
      cases payload
      rfl
    rw [optionEq]
    cases first : payload.data[0]? with
    | none => simp
    | some byte =>
      by_cases equal : byte = 0xef
      · subst byte; decide
      · simp [equal, bne_iff_ne]

/-- Native UInt256 remaining gas does not wrap after canonical prefix debit. -/
theorem constructor_remaining_nat (payload : ByteArray) (gas : UInt256) :
    (UInt256.ofNat (gas.toNat - Verity.Core.Model.MidnightInitcode.prefixCost payload.size)).toNat =
      gas.toNat - Verity.Core.Model.MidnightInitcode.prefixCost payload.size := by
  change (gas.toNat - _) % UInt256.size = _
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) gas.val.isLt)

/-- Once the prefix is funded, native deposit sufficiency is exactly the
canonical combined constructor and code-deposit budget. -/
theorem constructor_deposit_budget (payload : ByteArray) (gas : UInt256)
    (funded : Verity.Core.Model.MidnightInitcode.prefixCost payload.size ≤ gas.toNat) :
    GasConstants.Gcodedeposit * payload.size ≤
        (UInt256.ofNat (gas.toNat - Verity.Core.Model.MidnightInitcode.prefixCost payload.size)).toNat ↔
      Verity.Core.Model.MidnightInitcode.prefixCost payload.size + 200 * payload.size ≤ gas.toNat := by
  rw [constructor_remaining_nat]
  change 200 * payload.size ≤ gas.toNat - _ ↔ _
  omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
