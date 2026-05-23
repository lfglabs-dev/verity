# Ink xStocks Review Filtered Findings

Source review report: `docs/ink-xstocks-review-problems.md`.

This is the filtered triage of the GPT-5.5 high-thinking review. Items marked
implemented were fixed in this worktree. Items marked deferred are real
follow-up candidates, but are not blockers for the current proof-of-concept as
long as the docs keep the POC scope explicit.

## Implemented

### Coverage/status metadata was stale

Decision: implement.

The reviewer was correct at the time of review: five XStockVault theorem names
were missing from `test/property_manifest.json`, the matching property coverage
tags/tests were incomplete, and the generated verification status files were
stale.

Fix:

- Regenerated `test/property_manifest.json`; XStockVault now tracks all 13
  theorem names.
- Added property coverage in `test/PropertyXStockVault.t.sol` for:
  `syncFromBalanceOf_preserves_unrelated_storage`,
  `deposit_spec_preserves_multiplier_epoch`,
  `deposit_spec_preserves_pause_flag`,
  `withdraw_spec_preserves_multiplier_epoch`, and
  `withdraw_spec_preserves_pause_flag`.
- Regenerated/synced `artifacts/verification_status.json`,
  `docs/VERIFICATION_STATUS.md`, `README.md`, `docs-site/public/llms.txt`, and
  `PrintAxioms.lean`.

Verification: `make check` now passes end to end.

## Deferred

### Direct implementation-level deposit/withdraw correctness proofs

Decision: defer.

This is a valid limitation. The current proofs include specs and spec-level
lemmas, but do not yet prove the executable `deposit` and `withdraw` bodies
satisfy those specs across success and guarded revert paths.

Why not implement now: this expands the POC from xStocks integration-model
proofs into full function-body correctness for the example vault. That is
worth doing before calling XStockVault a complete verified contract, but it is
not required for the current documented POC boundary.

Recommended next action: add direct success theorems plus paused, stale epoch,
insufficient balance/assets/supply, and overflow-revert theorems before
promoting XStockVault beyond "baseline/model POC".

### Corporate-action claim scaling vs executable 1:1 withdraw accounting

Decision: defer, with scope caveat retained.

The reviewer is correct that the Rat-level theorem
`corporate_action_preserves_fraction_and_scales_claim` is an economic model
lemma. It is not a theorem about the current executable `withdraw`, which burns
shares 1:1 against `totalAssets`.

Why not implement now: changing executable withdraw to proportional accounting
would materially change the example contract and require a wider correctness
surface. The current docs already state that this is an economic model lemma
and that a full implementation-level corporate-action transition theorem is
not proved.

Recommended next action: if this should become a production-style vault
reference, replace 1:1 withdrawal with proportional redemption after
corporate-action sync and prove the implementation-level transition.

### Corporate-action property-test coverage is weaker than the Lean theorem

Decision: defer.

The reviewer is correct that the Solidity property mapped to
`corporate_action_preserves_fraction_and_scales_claim` checks only that epoch
updates do not remint shares. It does not test Rat-level claim scaling.

Why not implement now: the theorem is a pure economic model lemma over `Rat`,
while the Solidity harness exercises the skeleton contract. A faithful runtime
test would need a dedicated model harness or the proportional accounting change
described above.

Recommended next action: either add a dedicated model/harness test for claim
scaling, or classify that theorem as model-only/proof-only if the coverage
policy should require runtime tests to match theorem semantics exactly.

### Overflow behavior in deposit success specs/tests

Decision: defer with the direct correctness proof work.

The implementation uses `safeAdd`, while `deposit_spec` describes successful
post-state arithmetic with `add`. The current Solidity properties use
`uint128`, so they do not exercise full `Uint256` overflow boundaries.

Why not implement now: the right fix is to split deposit correctness into
non-overflow success preconditions and explicit overflow-revert cases. That
belongs with the direct implementation-level deposit proof work.

Recommended next action: add non-overflow preconditions and overflow-revert
specs/tests for share balance, total assets, and total supply additions.

### Generated guarded-function macro artifact

Decision: defer.

The reviewer is correct that
`artifacts/macro_property_tests/PropertyXStockVault.t.sol` contains generated
no-revert checks that are not valid for guarded calls without setup.

Why not implement now: this is a generator limitation, not a defect in the
manual XStockVault proof model. `make check` still passes because the macro
artifact health check treats the artifact as generated output, not the manual
semantic property suite.

Recommended next action: update the generator to skip unconditional no-revert
checks for guarded functions, or teach it to generate valid setup and arguments.

### Permissionless admin/oracle-like functions

Decision: defer as intentional POC scope.

The reviewer is correct that `setCorporateActionPaused`,
`updateMultiplierEpoch`, and `syncFromBalanceOf` are unsafe if copied into a
deployable contract as-is. The current Lean and Solidity files document this as
an accounting skeleton where access control and oracle authorization are outside
scope.

Recommended next action: add owner/oracle authorization only if this example is
intended to become a deployable builder reference rather than a proof POC.

## Verification

Passed locally:

- `lake build`
- `lake build Contracts.XStockVault Verity.Specs.Ink`
- `make check`
- `python3 scripts/check_property_manifest.py`
- `python3 scripts/check_property_coverage.py`
- `python3 scripts/check_property_manifest_sync.py`
- `python3 scripts/check_verification_status_doc.py`
- `python3 scripts/update_doc_numbers.py --check`

Not run:

- Foundry tests. `forge` is not installed in this environment.
