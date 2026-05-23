import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Verity.Specs.Common

/-!
Reusable assumptions for contracts integrating xStocks on Ink/EVM chains.

This module models the integration boundary only. It does not prove the
xStocks issuer, custody, backing, oracle, bridge, or token implementation.
-/

namespace Verity.Specs.Ink.XStocks

open Verity

abbrev MultiplierEpoch := Nat

structure XStockSnapshot where
  rawVaultBalance : Rat
  multiplier : Rat
  evmBalanceOfVault : Rat

def evmAdjustedBalance (x : XStockSnapshot) : Rat :=
  x.rawVaultBalance * x.multiplier

def evmBalanceOfIncludesMultiplier (x : XStockSnapshot) : Prop :=
  x.evmBalanceOfVault = evmAdjustedBalance x

def usesEvmBalanceExactlyOnce (assetAmount : Rat) (x : XStockSnapshot) : Prop :=
  assetAmount = x.evmBalanceOfVault

def doesNotApplyMultiplierAgain (assetAmount : Rat) (x : XStockSnapshot) : Prop :=
  assetAmount ≠ x.evmBalanceOfVault * x.multiplier

theorem direct_balance_use_uses_evm_balance_exactly_once
    (x : XStockSnapshot) :
    usesEvmBalanceExactlyOnce x.evmBalanceOfVault x := by
  rfl

theorem direct_balance_use_does_not_double_apply_multiplier
    (x : XStockSnapshot)
    (hBalancePositive : x.evmBalanceOfVault ≠ 0)
    (hMultiplierNotOne : x.multiplier ≠ 1) :
    doesNotApplyMultiplierAgain x.evmBalanceOfVault x := by
  intro h
  have hmul : x.evmBalanceOfVault * x.multiplier = x.evmBalanceOfVault := h.symm
  have hfactor : x.evmBalanceOfVault * (x.multiplier - 1) = 0 := by
    calc
      x.evmBalanceOfVault * (x.multiplier - 1)
          = x.evmBalanceOfVault * x.multiplier - x.evmBalanceOfVault := by ring
      _ = 0 := by rw [hmul]; ring
  have hzero_or := mul_eq_zero.mp hfactor
  cases hzero_or with
  | inl hbal => exact hBalancePositive hbal
  | inr hdiff =>
      apply hMultiplierNotOne
      linarith

end Verity.Specs.Ink.XStocks
