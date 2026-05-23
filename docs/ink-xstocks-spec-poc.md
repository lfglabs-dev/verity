# Ink xStocks Verity Spec POC

This POC shows how an Ink developer can formally verify a contract that uses xStocks.

It does not verify xStocks itself. It gives reusable models and specs for contracts built on top of xStocks.

## Why xStocks Need Special Specs

Normal ERC-20 integrations usually reason about balances and transfers. xStocks add corporate-action behavior: dividends, splits, reverse splits, and multiplier/rebasing mechanics.

If a vault treats xStocks like a normal ERC-20, it can double-count the multiplier, misprice shares across dividends or splits, or settle old deposit quotes after a corporate-action update.

## Example Contract

`Contracts/XStockVault/XStockVault.lean` models the accounting side of a vault that receives settled adjusted xStock amounts and mints vault shares. Token custody, transfer success, and oracle/admin authorization are intentionally outside this POC. It stores a multiplier epoch and a pause flag so state-changing accounting actions can reject stale quotes around corporate-action updates.

The reusable xStocks assumptions live in `Verity/Specs/Ink/XStocks.lean`.

## Invariants

1. EVM xStock `balanceOf()` is used exactly once.

What can go wrong: a vault computes `balanceOf(vault) * multiplier` on Ink even though EVM xStock `balanceOf()` is already equity-adjusted.

What the spec proves: the xStocks sync model stores the EVM `balanceOf()` amount directly and does not apply the multiplier a second time.

Lean theorem: `Contracts.XStockVault.Proofs.XStocks.sync_uses_evm_adjusted_balance_exactly_once`.

Note: the theorem's value-level "not double-applied" inequality assumes a nonzero adjusted balance and a multiplier different from `1`, because multiplying zero or multiplying by one is observationally indistinguishable from using the balance directly.

2. Corporate actions scale user claims but preserve vault share fractions.

What can go wrong: a vault tries to handle dividends, splits, or reverse splits by reminting shares, changing user ownership percentages.

What the spec proves: the economic model lemma for a multiplier update changes total assets by the multiplier ratio while leaving total shares and per-user share balances unchanged, so each user's share fraction is preserved and their claim scales proportionally. The current Lean contract exposes the accounting pieces for epoch updates and adjusted-balance sync separately; it does not yet prove a full implementation-level corporate-action transition theorem.

Lean theorem: `Contracts.XStockVault.Proofs.XStocks.corporate_action_preserves_fraction_and_scales_claim`.

3. Stale multiplier epochs cannot settle deposits.

What can go wrong: a user previews a deposit under one multiplier epoch and settles after a corporate-action update, minting too many or too few shares.

What the spec proves: a deposit quote whose epoch does not match the vault's current xStock multiplier epoch leaves vault state unchanged.

Lean theorem: `Contracts.XStockVault.Proofs.XStocks.stale_multiplier_epoch_cannot_settle_deposit`.

## How To Use This In Your Own Protocol

- Replace the accounting skeleton with your vault, wrapper, collateral adapter, or strategy.
- Keep the xStocks model boundary explicit: on Ink/EVM, `balanceOf()` is the adjusted balance.
- Add your production custody, transfer, access-control, and oracle authorization boundaries before treating the example as deployable.
- Add an epoch or pause-window guard to quote and settlement flows.
- Prove the xStocks-specific invariants first, then add protocol-specific accounting, collateral, or fee invariants.
- If integer rounding matters, adapt the Rat model to bounded integer lemmas after the economic invariant is clear.

## Future Modules

The same architecture can be extended to:

- Tydro integration specs: lending adapters, collateral accounting, health-factor assumptions.
- Nado integration specs: strategy vaults, PnL settlement, margin limits, fees and funding accounting.

## What This Does Not Prove

- It does not prove xStocks are 1:1 backed.
- It does not prove issuer, custodian, proof-of-reserves, or legal claims.
- It does not prove market price correctness.
- It does not prove xStocks core contracts or bridge behavior.
- It does not prove Tydro or Nado core.
- It only proves the integrating contract respects the stated xStocks assumptions.
