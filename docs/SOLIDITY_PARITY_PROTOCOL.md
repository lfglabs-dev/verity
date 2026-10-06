# Solidity-to-Verity Yul Parity Protocol

Issue: [#967](https://github.com/lfglabs-dev/verity/issues/967)

This document defines the recommended protocol for proving Yul-output identity against `solc` for an existing Solidity contract while preserving Verity's default compiler behavior.

## Goal

For a pinned toolchain tuple, make Verity emit Yul that is AST-identical to `solc`, with all compatibility behavior explicit, deterministic, and proof-gated.

## Scope and Design Boundary

1. Keep default Verity compilation semantics unchanged.
2. Put Solidity-compatibility rewrites behind an explicit parity pack (`--parity-pack`).
3. Require proof-linked rewrite activation (fail closed if proof metadata/registry is invalid).
4. Track any remaining non-identity gap as machine-checkable `unsupported` items.

This is not a one-off Morpho patch path. Morpho is the current target corpus driving the first parity-pack iterations.

## Inputs You Must Pin

1. Solidity compiler version/commit.
2. Optimizer settings (enabled/runs/viaIR).
3. EVM version.
4. Source set and build flags.
5. Verity revision and selected parity pack.

Without pinning these, exact Yul identity is not a meaningful claim.

## Protocol

1. Establish baseline artifacts.
   - Compile the same sources with `solc` and with Verity under a pinned parity pack.
   - Store both Yul outputs and tuple metadata as CI artifacts.
2. Run AST-level gap analysis.
   - Compare at AST/function-block level, not just text.
   - Emit deterministic reports (mismatch keys, digests, family summaries, unsupported manifest checks).
3. Classify mismatch families.
   - Prefer family-level structural classes (ABI helper layout, memory copy helpers, allocation helpers, dispatcher shape) over per-function ad-hoc fixes.
   - Separate rename-only deltas from structural deltas.
4. Implement compatibility rewrites in Verity.
   - Add rules in an explicit compat rewrite bundle in an external plugin package.
   - Keep rule scope tight (`ExprRule`/`StmtRule`/`BlockRule`/`ObjectRule` + `RewriteCtx` scope checks).
   - Attach proof references and pack allowlist membership.
5. Enforce pack-level proof composition.
   - Ensure pack proof registry is a subset of the selected bundle allowlist.
   - Fail closed at pack selection when composition/proof metadata is invalid.
6. Gate with CI.
   - Identity check: fail on unexpected mismatch.
   - Unsupported manifest: fail on drift/new unapproved mismatch categories.
   - Keep deterministic report artifacts for review and audit.
7. Iterate to zero mismatch.
   - Remove unsupported entries as each family is solved.
   - Flip final gate to strict zero-mismatch identity for pinned targets.

## Using an LLM Translation as Starting Point

Using an LLM-generated Verity model from Solidity is acceptable as an initial scaffold, but parity claims only come from the protocol above:

1. Model translation quality is treated as an input assumption.
2. Yul identity is established by deterministic diff reports + proof-gated rewrite convergence.
3. Final acceptance is CI evidence (identity gate + empty/approved unsupported manifest), not model provenance.

## What "Proven Patches" Means Here

In this protocol, a patch is "proven" only when:

1. It has explicit matcher/rewrite metadata.
2. It has a non-empty proof reference.
3. The proof reference is present in the active proof registry.
4. The rule is in scope for the active rewrite context.
5. The selected parity pack passes composition validation.

If any condition fails, activation fails closed.

## Reuse Beyond Morpho

The method is generic and reusable for any Solidity contract set, as long as you:

1. pin tuple metadata;
2. create/select the matching parity pack;
3. add proof-gated compat rewrites only for observed mismatch families;
4. enforce identity/unsupported gates in CI.

Different projects may require different compat families, but the control plane (packs, bundles, proof registry, deterministic reports) remains the same.

## Related

- [`SOLIDITY_PARITY_PROFILE.md`](SOLIDITY_PARITY_PROFILE.md)
- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`IDENTITY_CHECKER.md`](IDENTITY_CHECKER.md)


### Stateful sequence reduction

The reducer first tries deleting contiguous chunks while preserving the original
first mismatch category. It then checks single-transaction deletions and replays
the final witness from the original pre-state. The chunk pass reduces repeated
full-sequence execution for long campaigns; it does not change transaction
inputs, observations, compiler settings, replay limits or the requirement for a
reproduced deletion-minimal witness. Resource and instrumentation failures
propagate. An exhausted attempt budget still reports `deletion_minimal: false`.

Protocol regressions cover a 64-transaction sequence with ordered setup and
failure dependencies, a chunk replay failure, and exhausted-budget minimality.
A real fixed-array layout mutant campaign remains required before claiming the
new reducer works end to end.


### Experimental cached Denote driver

`check_stateful --cached-denote` is an opt-in prototype. The adapter elaborates
an exact copy of the model driver once using the pinned actual Lean toolchain,
then imports the emitted module and executes its original `main` for every
sequence replay. It retains the ordinary implementation identity check and
additionally records and checks cached source, wrapper and module artifacts
before and after execution. The uncached route remains the default.

Seven cache-lifecycle tests cover reuse, source/artifact/wrapper changes, added
modules, failed compilation and missing artifacts. These tests mock the compiler
and do **not** establish that cached Lean execution works. Native cold/cached
A/B/C campaigns and a cached runtime mutation with final minimal-witness replay
remain mandatory before enabling this path in release campaigns. Cached replay
files archive all added artifact hashes; ordinary observations and reduction
requirements are unchanged.
