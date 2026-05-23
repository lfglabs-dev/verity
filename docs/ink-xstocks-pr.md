# POC: Ink xStocks reusable specs for Verity

## Summary

This draft branch adds a small Ink xStocks proof-of-concept to Verity. The goal is to show how Ink builders can verify their own contracts that integrate xStocks without claiming to verify the xStocks protocol itself.

## What The POC Proves

- EVM xStock `balanceOf()` is used exactly once by the vault sync model. The value-level inequality proof assumes a nonzero adjusted balance and a multiplier different from `1`.
- The economic corporate-action model scales user claims while preserving vault share fractions.
- Stale multiplier epochs cannot settle deposit quotes in the model.

## What It Does Not Prove

- xStocks backing, custody, legal structure, proof of reserves, or issuer behavior.
- xStocks core contract correctness.
- Market prices, oracle behavior, or bridge correctness.
- Token custody, transfer success, production access control, or oracle authorization.
- A full implementation-level theorem connecting the contract's epoch-update and balance-sync functions into one corporate-action transition.
- Tydro or Nado core protocol behavior.

## New Surfaces

- Reusable model: `Verity/Specs/Ink/XStocks.lean`
- Example contract: `Contracts/XStockVault/XStockVault.lean`
- Headline proofs: `Contracts/XStockVault/Proofs/XStocks.lean`
- Research notes: `docs/ink-xstocks-research.md`
- Builder-facing docs: `docs/ink-xstocks-spec-poc.md`

## Verification

- [x] `lake build`
- [x] `make check`
- [x] `python3 scripts/check_contract_structure.py`
- [x] `python3 scripts/check_storage_layout.py`
- [x] `python3 scripts/check_paths.py`
- [x] `python3 scripts/check_lean_hygiene.py`
- [x] `python3 scripts/check_property_manifest.py`
- [x] `python3 scripts/check_property_coverage.py`

## Review Follow-Up

- Implemented the review-blocking coverage/status sync issue from `docs/ink-xstocks-review-filtered.md`.
- Added property coverage for all 13 XStockVault theorem names and regenerated the verification status artifact/docs.
- Kept the broader implementation-level and production-hardening findings documented as deferred POC follow-ups.

## Follow-Up Modules

- Tydro: lending adapter specs for supply, borrow, repay, withdraw, collateral, and health assumptions.
- Nado: strategy/vault specs around settlement, PnL, fees, funding, and margin risk.
