# Yul Identity Checker

Issue: [#967](https://github.com/lfglabs-dev/verity/issues/967)

This document defines the target workflow for checking AST-level identity between Verity-generated Yul and `solc`-generated Yul for pinned toolchain tuples.

## Status

Not implemented. A prototype report generator and metrics gate were never wired
into CI and have been removed; this page records the intended workflow.

## Goals

1. Compare Yul at AST level (not text-only).
2. Localize mismatches to stable node paths and source/IR origins.
3. Produce machine-readable reports for CI and rule authoring.
4. Distinguish `non-identity` from `unsupported`.

## Report Schema

1. `status`: `identical | non_identical`.
2. `summary`: file + mismatch counts (and by-kind totals).
3. `mismatches[]`: stable entries with:
   - `file`
   - `path` (function/subtree-localized path)
   - `kind`
   - `verity` and `solc` values

## CI Integration

1. Run identity checker on pinned fixture corpus.
2. Fail on `non_identical` (use `--max-mismatches` for known transient single deltas, e.g. during 1982 dynamic ABI development).
3. Allow `unsupported` only if listed in tracked manifest.
4. Upload JSON reports as workflow artifacts.

## Related

- [`PARITY_PACKS.md`](PARITY_PACKS.md)
- [`REWRITE_RULES.md`](REWRITE_RULES.md)
- [`SOLIDITY_PARITY_PROTOCOL.md`](SOLIDITY_PARITY_PROTOCOL.md)
