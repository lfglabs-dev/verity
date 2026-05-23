# Ink xStocks / XStockVault Review Problems

Review scope: current worktree for `Verity.Specs.Ink`, `Contracts.XStockVault`, Solidity examples/tests, property manifests/artifacts, README/docs-site presentation, and touched build/test scripts.

## Problems

### Critical: coverage/status metadata is out of sync with the current theorem set

Evidence:

- `Contracts/XStockVault/Proofs/Correctness.lean:15`
- `Contracts/XStockVault/Proofs/Correctness.lean:32`
- `Contracts/XStockVault/Proofs/Correctness.lean:40`
- `Contracts/XStockVault/Proofs/Correctness.lean:48`
- `Contracts/XStockVault/Proofs/Correctness.lean:56`
- `test/property_manifest.json:309`
- `docs/VERIFICATION_STATUS.md:200`
- `artifacts/verification_status.json:36`

`check_property_coverage.py` fails because five XStockVault theorems are present in Lean but absent from `test/property_manifest.json`: `syncFromBalanceOf_preserves_unrelated_storage`, `deposit_spec_preserves_multiplier_epoch`, `deposit_spec_preserves_pause_flag`, `withdraw_spec_preserves_multiplier_epoch`, and `withdraw_spec_preserves_pause_flag`. The docs/artifact still report XStockVault as `100% (8/8)`, which is stale for the current worktree.

Recommended action: regenerate/sync the property manifest and verification artifacts, then add real property tests for the five theorems or mark them as proof-only exclusions if they cannot be tested meaningfully.

### Major: deposit and withdraw are specified, but not proved against the implementation

Evidence:

- `Contracts/XStockVault/XStockVault.lean:43`
- `Contracts/XStockVault/XStockVault.lean:59`
- `Contracts/XStockVault/Spec.lean:31`
- `Contracts/XStockVault/Spec.lean:40`
- `Contracts/XStockVault/Proofs/Correctness.lean:24`
- `docs/VERIFICATION_STATUS.md:40`
- `README.md:30`

The core state-changing functions have specs, but the current correctness proofs are facts about those spec predicates after assuming they already hold. There is no implementation-level theorem that the `deposit` or `withdraw` function body satisfies the success spec, nor the paused/stale/insufficient/overflow failure cases.

Recommended action: add direct function-body correctness theorems for successful `deposit` and `withdraw`, plus revert theorems for guarded paths. Until then, keep docs/status language at "baseline/model lemmas" rather than implying complete vault behavior is verified.

### Major: the corporate-action claim model does not match the executable withdraw accounting

Evidence:

- `Contracts/XStockVault/Spec.lean:86`
- `Contracts/XStockVault/Spec.lean:89`
- `Contracts/XStockVault/Proofs/XStocks.lean:21`
- `Contracts/XStockVault/XStockVault.lean:67`
- `Contracts/XStockVault/XStockVault.lean:71`
- `docs/ink-xstocks-spec-poc.md:35`

The pure model proves user claims scale with `totalAssets / totalShares`, but the executable `withdraw` burns `shares` and subtracts the same `shares` amount from `totalAssets`. After `syncFromBalanceOf` changes assets while supply stays fixed, that 1:1 withdrawal rule is no longer proportional to the modeled claim.

Recommended action: either change the executable/spec withdrawal model to use proportional assets after corporate actions, or narrow the corporate-action theorem/docs so it is clearly not a property of the current executable vault accounting.

### Major: the property test mapped to the corporate-action theorem does not test claim scaling

Evidence:

- `test/property_manifest.json:310`
- `test/PropertyXStockVault.t.sol:47`
- `test/PropertyXStockVault.t.sol:54`
- `Contracts/XStockVault/Proofs/XStocks.lean:21`

`corporate_action_preserves_fraction_and_scales_claim` is counted as covered, but the Solidity property only calls `updateMultiplierEpoch` and checks that shares/supply did not change. It never changes `totalAssets`, checks a multiplier ratio, or verifies a user claim.

Recommended action: replace this with a test/harness that exercises the economic model being claimed, or remove the theorem from property-test coverage and classify it as proof-only/model-only.

### Major: overflow behavior is not represented in the success spec or property tests

Evidence:

- `Contracts/XStockVault/XStockVault.lean:50`
- `Contracts/XStockVault/XStockVault.lean:52`
- `Contracts/XStockVault/XStockVault.lean:54`
- `Contracts/XStockVault/Spec.lean:34`
- `Contracts/XStockVault/Spec.lean:35`
- `Contracts/XStockVault/Spec.lean:36`
- `test/PropertyXStockVault.t.sol:24`
- `test/XStockVault.t.sol:48`

The implementation uses `safeAdd` and reverts on overflow, while `deposit_spec` states modular `add` postconditions without non-overflow preconditions. The Solidity tests use `uint128`, so they avoid the `Uint256` overflow boundary.

Recommended action: split deposit correctness into non-overflow success preconditions and explicit overflow-revert cases for share balance, total assets, and total supply.

### Minor: generated macro property artifact contains impossible no-revert checks

Evidence:

- `artifacts/macro_property_tests/PropertyXStockVault.t.sol:38`
- `artifacts/macro_property_tests/PropertyXStockVault.t.sol:44`
- `Contracts/XStockVault/XStockVault.lean:43`
- `Contracts/XStockVault/XStockVault.lean:59`

The generated artifact asserts that `deposit(1, 1)` and `withdraw(1, 1)` should not unexpectedly revert. The constructor leaves `multiplierEpoch = 0`, so both calls hit the stale-epoch guard; `withdraw` also lacks shares.

Recommended action: teach the generator to skip unconditional no-revert checks for guarded functions, or generate valid setup/arguments for guarded functions.

### Minor: permissionless admin/oracle-like functions remain unsafe if copied as a reference

Evidence:

- `examples/solidity/XStockVault.sol:28`
- `examples/solidity/XStockVault.sol:35`
- `examples/solidity/XStockVault.sol:39`
- `Contracts/XStockVault/XStockVault.lean:33`
- `Contracts/XStockVault/XStockVault.lean:37`
- `Contracts/XStockVault/XStockVault.lean:40`

The docs say access control and oracle authorization are out of scope, but the Solidity example is still easy to copy. Any caller can pause/unpause, change the epoch, or set total assets.

Recommended action: add owner/oracle authorization before presenting the Solidity as a builder reference, or make the file/test names and comments explicitly say this is an unsafe accounting skeleton.

## Verification performed

Passed:

- `lake build`
- `lake build Contracts.XStockVault Verity.Specs.Ink`
- `python3 scripts/check_contract_structure.py`
- `python3 scripts/check_property_manifest.py`
- `python3 scripts/check_macro_property_test_generation.py --check`
- `python3 scripts/check_verification_status_doc.py`
- `python3 scripts/check_axioms.py`
- `python3 scripts/check_lean_hygiene.py`
- `python3 scripts/check_paths.py`
- `python3 scripts/check_package_glob_surfaces.py`
- `python3 scripts/check_package_import_boundaries.py`
- `python3 scripts/check_split_package_builds.py`
- `python3 scripts/check_storage_layout.py`
- `python3 scripts/check_verify_sync.py`
- `python3 scripts/test_profile_ci_resources.py`

Failed:

- `python3 scripts/check_property_coverage.py` failed with five missing XStockVault theorem mappings.
- `python3 scripts/generate_verification_status.py --check` reported `artifacts/verification_status.json` as stale.
- `forge test --match-contract 'XStockVault|PropertyXStockVaultTest'` failed immediately because `forge` is not installed.

Not completed:

- `lake exe verity-compiler --module Contracts.XStockVault.XStockVault -o /tmp/xstockvault-yul` was stopped after the local toolchain reported `could not execute external process 'cc'` while building native FFI and then continued compiling for an extended time.
