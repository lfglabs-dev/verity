import Contracts.XStockVault.Spec

namespace Contracts.XStockVault.Invariants

open Verity
open Contracts.XStockVault.Spec
open Verity.Specs.Ink.XStocks

structure WellFormedXStockVault (s : ContractState) : Prop where
  sender_nonzero : s.sender ≠ 0
  contract_nonzero : s.thisAddress ≠ 0
  pause_is_boolean : s.storage 5 = 0 ∨ s.storage 5 = 1

def quoteEpochMatches (s : VaultState) (q : DepositQuote) : Prop :=
  q.multiplierEpoch = s.xstockMultiplierEpoch

def corporateActionDoesNotRemintShares (s s' : VaultState) : Prop :=
  s'.totalShares = s.totalShares ∧ s'.shareBalance = s.shareBalance

def usesAdjustedBalanceFromEvm (assetAmount : Rat) (x : XStockSnapshot) : Prop :=
  usesEvmBalanceExactlyOnce assetAmount x ∧ doesNotApplyMultiplierAgain assetAmount x

end Contracts.XStockVault.Invariants
