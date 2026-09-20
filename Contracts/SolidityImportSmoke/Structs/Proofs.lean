import Contracts.SolidityImportSmoke.Structs.Spec
import Verity.Proofs.Stdlib.SolidityImport

namespace Contracts.SolidityImportSmoke.Structs.Proofs
open Verity
open Verity.Proofs.Stdlib.SolidityImport
open Contracts.SolidityImportSmoke.Structs.Store
open Spec

theorem set_then_get (s post : ContractState) (amount : Uint256) (who : Address)
    (h : (set (amount, who)).run s = .success () post) :
    set_spec amount who (view s) (view post) := by
  unfold set_spec
  cases hbeq : Nat.beq s.msgValue.val 0
  · solidity_simp
  · solidity_simp
    subst h
    solidity_simp

theorem other_member_unchanged_thm (s post : ContractState) (amount : Uint256) (who : Address)
    (h : (set (amount, who)).run s = .success () post) :
    other_member_unchanged (amount, who) (view s) (view post) :=
  (set_then_get s post amount who h).2

theorem get_meets_spec (s : ContractState) (h0 : s.msgValue = 0) :
    ∃ post, get.run s = ContractResult.success ((view s).data_amount, (view s).data_who) post := by
  solidity_simp

theorem make_encodes (s : ContractState) (amount : Uint256) (who : Address)
    (h0 : s.msgValue = 0) :
    ∃ post, (make amount who).run s = ContractResult.success (amount, who) post := by
  solidity_simp

end Contracts.SolidityImportSmoke.Structs.Proofs
