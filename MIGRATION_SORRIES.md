# Lean 4.31 downstream scaffolding: temporary-hole ledger

**Status: NON CERTIFIÉE. NON MERGEABLE vers `main`.** This branch is an
isolated downstream-authoring scaffold based on PR #2210. It is not the
official migration branch, does not certify that migration, and must not be
merged into `main` until the official Lean 4.31 migration is green.

## Exact base

- Repository: `lfglabs-dev/verity`
- PR: [#2210](https://github.com/lfglabs-dev/verity/pull/2210)
- Public PR head used as the branch parent:
  `46d17e581b9cb5526ac930d37f8e8bcef196c6c6`
- Source fetched explicitly as `refs/pull/2210/head`.
- Toolchain: `leanprover/lean4:v4.31.0`
- EVMYulLean pin (unchanged):
  `f7e4ee0dc8f8d5265ce822a937ab5be771f182e9`

## Policy

Temporary `sorry` or `admit` is permitted only in new downstream-scaffolding
Lean modules and only next to the blocked obligation. It is prohibited in EVM
or Yul semantics, correction bridges, reference compilation theorems, and all
official migration files. Every temporary hole must have one ledger entry
below, with its file/declaration, exact obligation type, reason, dependents,
and removal condition. `scripts/check_migration_sorries.py` enforces this
ledger; `--certify` requires no entries and no holes.

## Machine-readable inventory

<!-- MIGRATION_SORRIES_JSON_BEGIN -->
```json
{
  "schema": 1,
  "base_pr": 2210,
  "base_head": "46d17e581b9cb5526ac930d37f8e8bcef196c6c6",
  "entries": [],
  "zero_sorries": true,
  "note": "The initial canary is fully proved; no temporary sorry/admit is necessary."
}
```
<!-- MIGRATION_SORRIES_JSON_END -->
