import Contracts.XStockVault.Proofs.Basic
import Contracts.XStockVault.Proofs.XStocks

namespace Contracts.XStockVault.Proofs.Correctness

open Verity
open Contracts.XStockVault.Spec

theorem syncFromBalanceOf_sets_assets_to_adjusted_balance
    (adjustedBalanceOfVault : Uint256)
    (s s' : ContractState)
    (h : syncFromBalanceOf_spec adjustedBalanceOfVault s s') :
    s'.storage 1 = adjustedBalanceOfVault := h.1

theorem syncFromBalanceOf_preserves_unrelated_storage
    (adjustedBalanceOfVault : Uint256)
    (s s' : ContractState)
    (slotIdx : Nat)
    (h : syncFromBalanceOf_spec adjustedBalanceOfVault s s')
    (hSlot : slotIdx ≠ 1) :
    s'.storage slotIdx = s.storage slotIdx := by
  exact h.2.2.2.2.1 slotIdx hSlot

theorem stale_epoch_deposit_spec_impossible
    (assets quoteEpoch : Uint256)
    (s s' : ContractState)
    (hSpec : deposit_spec assets quoteEpoch s s')
    (hStale : quoteEpoch ≠ s.storage 4) :
    False := by
  exact hStale hSpec.2.1

theorem deposit_spec_preserves_multiplier_epoch
    (assets quoteEpoch : Uint256)
    (s s' : ContractState)
    (hSpec : deposit_spec assets quoteEpoch s s') :
    s'.storage 4 = s.storage 4 := by
  rcases hSpec with ⟨_, _, _, _, _, _, hFrame, _, _⟩
  exact hFrame 4 (by decide) (by decide)

theorem deposit_spec_preserves_pause_flag
    (assets quoteEpoch : Uint256)
    (s s' : ContractState)
    (hSpec : deposit_spec assets quoteEpoch s s') :
    s'.storage 5 = s.storage 5 := by
  rcases hSpec with ⟨_, _, _, _, _, _, hFrame, _, _⟩
  exact hFrame 5 (by decide) (by decide)

theorem withdraw_spec_preserves_multiplier_epoch
    (shares quoteEpoch : Uint256)
    (s s' : ContractState)
    (hSpec : withdraw_spec shares quoteEpoch s s') :
    s'.storage 4 = s.storage 4 := by
  rcases hSpec with ⟨_, _, _, _, _, _, _, _, _, hFrame, _, _⟩
  exact hFrame 4 (by decide) (by decide)

theorem withdraw_spec_preserves_pause_flag
    (shares quoteEpoch : Uint256)
    (s s' : ContractState)
    (hSpec : withdraw_spec shares quoteEpoch s s') :
    s'.storage 5 = s.storage 5 := by
  rcases hSpec with ⟨_, _, _, _, _, _, _, _, _, hFrame, _, _⟩
  exact hFrame 5 (by decide) (by decide)

end Contracts.XStockVault.Proofs.Correctness
