import Compiler.Proofs.IRGeneration.NativeConstructorRuntimeGuard

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul

private theorem empty_code (bytes : ByteArray) (empty : bytes.size = 0) :
    bytes = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_iff_size_eq_zero.mpr empty

/-- Native successful-construction collision checking uses the real optional
account, consistently with the entry nonce/code criterion. -/
theorem constructor_vacancy_guard (accounts : AccountMap .EVM) (target : AccountAddress)
    (vacant : (accounts.getD target default).nonce = UInt256.ofNat 0 ∧
      (accounts.getD target default).code.size = 0) :
    (match accounts.get? target with
      | some account => decide (account.code ≠ ByteArray.empty ∨ account.nonce ≠ (⟨0⟩ : UInt256))
      | none => false) = false := by
  have view : accounts.getD target default = (accounts.get? target).getD default :=
    Std.TreeMap.getD_eq_getD_getElem?
  rw [view] at vacant
  cases found : accounts.get? target with
  | none => rfl
  | some account =>
    rw [found] at vacant
    have code := empty_code account.code vacant.2
    have nonce : account.nonce = (⟨0⟩ : UInt256) := vacant.1
    simp only [code, nonce, ne_eq, not_true_eq_false, or_self, decide_false]

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
