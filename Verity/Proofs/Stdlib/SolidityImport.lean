import Lean
import Verity.Core
import Verity.Core.Invariant
import Verity.Core.SolidityImportAttr
import Verity.Stdlib.Math
import Verity.EVM.Uint256

namespace Verity.Proofs.Stdlib.SolidityImport

open Verity
open Lean Parser.Tactic

/-- `Contract.run` either rolls back to the pre-state or returns a successful post-state. -/
theorem run_snd_cases {α : Type} (c : Contract α) (s : ContractState) :
    (c.run s).snd = s ∨ ∃ a post, c.run s = .success a post ∧ (c.run s).snd = post := by
  unfold Contract.run
  cases c s
  · exact Or.inr ⟨_, _, rfl, rfl⟩
  · exact Or.inl rfl

/-- The imported nonpayable guard tests `msgValue.val`; this relates it to `= 0`. -/
theorem uint256_eq_zero_iff (x : Verity.Core.Uint256) : x = 0 ↔ x.val = 0 := by
  constructor
  · intro h; subst h; exact Verity.Core.Uint256.val_zero
  · intro h; exact Verity.Core.Uint256.ext (h.trans Verity.Core.Uint256.val_zero.symm)

syntax (name := soliditySimpTac)
  "solidity_simp" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| solidity_simp) =>
      `(tactic| solidity_simp [])
  | `(tactic| solidity_simp [$args,*]) =>
      `(tactic| simp_all [solidity_import,
        $(mkIdent ``Contract.run):ident, $(mkIdent ``Bind.bind):ident, $(mkIdent ``Pure.pure):ident,
        $(mkIdent ``Verity.instMonadContract):ident, $(mkIdent ``Verity.bind):ident, $(mkIdent ``Verity.pure):ident,
        $(mkIdent ``msgValue):ident, $(mkIdent ``msgSender):ident, $(mkIdent ``Verity.require):ident,
        $(mkIdent ``getStorage):ident, $(mkIdent ``setStorage):ident, $(mkIdent ``getStorageAddr):ident,
        $(mkIdent ``setStorageAddr):ident, $(mkIdent ``getMapping):ident,
        $(mkIdent ``setMapping):ident, $(mkIdent ``Verity.Stdlib.Math.requireSomeUint):ident,
        $(mkIdent ``Verity.Stdlib.Math.safeAdd):ident, $(mkIdent ``Verity.Stdlib.Math.safeSub):ident,
        $(mkIdent ``Verity.EVM.Uint256.sub):ident, $(mkIdent ``Nat.not_le_of_lt):ident,
        $(mkIdent ``Nat.not_lt_of_ge):ident, $(mkIdent ``ContractState.readSlot):ident,
        $(mkIdent ``ContractState.writeSlot):ident, $(mkIdent ``ContractState.readAddrSlot):ident,
        $(mkIdent ``ContractState.writeAddrSlot):ident, $(mkIdent ``ContractState.readMap):ident,
        $(mkIdent ``ContractState.writeMap):ident, $(mkIdent ``ContractState.storage):ident,
        $(mkIdent ``ContractState.storageAddr):ident, $(mkIdent ``ContractState.storageMap):ident,
        $(mkIdent ``uint256_eq_zero_iff):ident,
        $args,*])

end Verity.Proofs.Stdlib.SolidityImport
