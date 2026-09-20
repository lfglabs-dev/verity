import Contracts.SolidityImportSmoke.Modifiers.Spec
import Verity.Proofs.Stdlib.SolidityImport

namespace Contracts.SolidityImportSmoke.Modifiers.Proofs
open Verity
open Verity.Proofs.Stdlib.SolidityImport
open Contracts.SolidityImportSmoke.Modifiers.Child
open Spec

theorem status_restored (s post : ContractState) (amount : Uint256)
    (h : (early amount).run s = .success amount post) :
    early_spec amount (view s) (view post) := by
  unfold early_spec
  by_cases h0 : s.msgValue = 0
  · by_cases hst : 1 < (view s).status.val
    · solidity_simp
    · solidity_simp
      subst h
      solidity_simp
  · solidity_simp

theorem early_meets_spec (s : ContractState) (amount : Uint256)
    (h0 : s.msgValue = 0) (harmed : (view s).status = 1) :
    ∃ post, (early amount).run s = ContractResult.success amount post ∧
      early_spec amount (view s) (view post) := by
  unfold early_spec
  solidity_simp

theorem guarded_success_spec (s post : ContractState) (amount : Uint256)
    (h : (guarded amount).run s = .success () post) :
    guarded_spec amount (view s) (view post) := by
  unfold guarded_spec
  by_cases h0 : s.msgValue = 0
  · by_cases ho : s.sender = (view s).owner
    · by_cases hp : (view s).paused.val = 0
      · solidity_simp
        subst h
        solidity_simp
      · solidity_simp
    · by_cases hp : (view s).paused.val = 0
      · solidity_simp
      · solidity_simp
  · solidity_simp

theorem tagged_uses_base_helper (s post : ContractState)
    (h : tagged.run s = .success () post) :
    tagged_spec (view s) (view post) := by
  unfold tagged_spec
  by_cases h0 : s.msgValue = 0
  · solidity_simp
    subst h
    solidity_simp
  · solidity_simp

theorem snapshot_restores_status (s post : ContractState) (amount : Uint256)
    (h : (snapshot amount).run s = .success amount post) :
    snapshot_spec amount (view s) (view post) := by
  unfold snapshot_spec
  by_cases h0 : s.msgValue = 0
  · solidity_simp
    subst h
    solidity_simp
  · solidity_simp

end Contracts.SolidityImportSmoke.Modifiers.Proofs
