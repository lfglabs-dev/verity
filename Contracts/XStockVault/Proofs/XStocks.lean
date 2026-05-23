import Contracts.XStockVault.Invariants

namespace Contracts.XStockVault.Proofs.XStocks

open Verity
open Contracts.XStockVault.Spec
open Verity.Specs.Ink.XStocks

theorem sync_uses_evm_adjusted_balance_exactly_once
    (s : VaultState)
    (x : XStockSnapshot)
    (_hEvmBalance : x.evmBalanceOfVault = evmAdjustedBalance x)
    (hBalancePositive : x.evmBalanceOfVault ≠ 0)
    (hMultiplierNotOne : x.multiplier ≠ 1) :
    (syncAssetsFromXStock s x).totalAssets = x.evmBalanceOfVault
      ∧ (syncAssetsFromXStock s x).totalAssets ≠ x.evmBalanceOfVault * x.multiplier := by
  constructor
  · rfl
  · exact direct_balance_use_does_not_double_apply_multiplier x hBalancePositive hMultiplierNotOne

theorem corporate_action_preserves_fraction_and_scales_claim
    (s : VaultState)
    (user : Address)
    (oldMultiplier newMultiplier : Rat)
    (_hOldPositive : oldMultiplier > 0)
    (_hNewPositive : newMultiplier > 0) :
    let s' := applyMultiplierUpdate s oldMultiplier newMultiplier
    shareFraction s' user = shareFraction s user
      ∧ userClaim s' user = userClaim s user * (newMultiplier / oldMultiplier) := by
  intro s'
  constructor
  · subst s'
    simp [shareFraction, applyMultiplierUpdate]
  · subst s'
    by_cases hShares : s.totalShares = 0
    · simp [userClaim, shareFraction, applyMultiplierUpdate, hShares]
    · simp [userClaim, shareFraction, applyMultiplierUpdate, hShares]
      ring_nf

theorem stale_multiplier_epoch_cannot_settle_deposit
    (s : VaultState)
    (q : DepositQuote)
    (hStale : q.multiplierEpoch ≠ s.xstockMultiplierEpoch) :
    settleDepositQuote s q = s := by
  simp [settleDepositQuote, hStale]

end Contracts.XStockVault.Proofs.XStocks
