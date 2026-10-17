# Native fork audit scope for the Solidity importer

The solidity_import mission requires exact agreement with the real EVM. That
requires an explicit extension of the original Issue #1722 audit scope, whose
initial policy admitted visibility and toolchain changes only. This document
records the two specific implementation changes in the new immutable dependency
pin. It does not authorize arbitrary semantic changes.

Verity pins `4cf4c5d0f286e8efc3d9e972ce3616bfe83a0624`. All 25 commits since the
recorded upstream base `047f63070309f436b66c61e276ab3b6d1169265a` are enumerated
in [the fork audit](../artifacts/evmyullean_fork_audit.json). The generator
rejects semantic changes outside the two commit identities below, rejects
mislabeling either as nonsemantic, and checks the identity and completeness of
the saved evidence. It still checks every package manifest against the same
exact pin.

## Structural jump scanner

`0ff72b2db35302305fccb1d4f42b480434b77bfe` replaces the opaque partial
`D_J_aux` over a UInt256 index with a structurally recursive scanner over Nat,
bounded by the bytecode length. It advances by the instruction width and skips
PUSH immediate bytes. Its included closed regression checks a PUSH1 immediate
that contains a JUMPDEST byte. This changes an implementation trusted by native
execution; it is not silently classified as visibility. No universal equivalence
to the old opaque scanner or full Ethereum conformance rerun is claimed.

## Osaka creation correction

`a4473c2c1831d99ac3e1c5be7c9ce8e07da04266` changes shared native `Lambda`:
it removes the unconditional proposed EIP-7610 persistent-storage collision
check and clears the new account's persistent storage before constructor
execution. Nonce and code collisions remain, as do the target balance and the
precreation target snapshot on failure. This affects CREATE as well as CREATE2;
the independent calibration below exercises CREATE2. The dependency does not
introduce a configurable fork selector or prove other fork variants.

The previous pin returns zero and retains slot9=77 for a zero-nonce, empty-code
target with that storage. Foundry v1.5.0, Osaka, succeeds and resets slot9 to0.
Removing only the collision predicate would wrongly retain storage on success.
The correction fixes both observations. This is required by the existing
mission's exact-EVM objective; a fabricated poststate would not satisfy it.

[The immutable evidence artifact](../artifacts/evmyullean_osaka_creation_reference.json)
archives the successful exact-head checks, strict native runtime, four real-EVM
cases and four production-semantics mutations with identical failure replay.
The source identities agree across the instruments. The cases cover storage-only
and balance-only successful targets and nonce/code collisions. Checks include
returned address, native gas, balance, persistent/original storage, creator
nonce, and native created-account membership. Full transaction traces remain
in the campaign receipts; the dependency scripts reproduce these cases.

Reproduce in a checkout of the exact native pin:

```sh
python3 -m pip install -r requirements-native-tests.txt
lake build EvmYul create2OsakaChecks EvmYul.FFI.ffi:dynlib
python3 scripts/check_create2_osaka_runtime.py --output .lake/osaka-runtime
python3 scripts/check_create2_osaka_mutations.py --output .lake/osaka-mutations
# Foundry v1.5.0 anvil and cast must be on PATH.
python3 scripts/check_create2_osaka_reference.py --output .lake/osaka-reference
```

A previous exit-zero runtime with an initialization PANIC was rejected. The
strict runtime requires the exact four-case marker and empty stderr; Python
precompile startup dependencies are pinned. An exit code alone is insufficient.

## Limits and release gates

Upstream conformance does not transfer by ancestry to changed transitions.
These four cases are component conformance evidence, not a full upstream suite,
a whole-transaction correspondence proof, or whole-Midnight A/B/C validation.
Native interpreter fuel is separate from EVM gas. CREATE2 can mask nested
interpreter exhaustion as creation failure, so the actual constructor must have
a proven sufficient fuel bound before it can authenticate importer admission.
Canonical/native postcreation accounts, rollback, source storage channels,
constructor output and gas all retain their separate obligations.

The pin update changes no Solidity admission and no golden model or pilot
provenance. Required exact-publication-head checks and small-PR merge gates still
apply; the native dependency PR remains a draft until its release gates pass.
