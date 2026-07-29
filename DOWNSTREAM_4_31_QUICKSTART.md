# Downstream Lean 4.31 quickstart (non-certified scaffold)

**This branch is NON CERTIFIÉE and NON MERGEABLE into `main`.** It is a
temporary authoring surface based on PR #2210, not the official migration.
The full build may fail on unfinished official migration obligations; that is
not hidden by this branch. Use only the targeted dev gate below.

## Get the exact branch

```bash
git clone https://github.com/lfglabs-dev/verity.git
cd verity
git fetch origin dev/lean-4.31-scaffolding
git switch --track origin/dev/lean-4.31-scaffolding
cat lean-toolchain  # leanprover/lean4:v4.31.0
```

## Write a contract, specification, and proof

Copy `Contracts/Smoke/Downstream431Canary.lean` to a new module under
`Contracts/Smoke/`. It contains a `verity_contract`, a `*_spec` proposition,
and two kernel-checked theorems. Keep any temporary hole local to a downstream
module and add its complete JSON ledger entry to `MIGRATION_SORRIES.md`.

## Run the development gate

```bash
set -o pipefail
lake build Contracts.Smoke.Downstream431Canary
python3 scripts/check_migration_sorries.py
python3 scripts/check_migration_sorries.py --certify
```

This is the stable, deliberately narrow gate: it checks the canary’s contract,
specification, and proofs with Lean 4.31, plus the temporary-hole ledger. It
does not claim that `lake build` for the whole repository is green.

## Move to the certified migration later

When the official PR #2210 migration is green and merged, replace this branch
with the certified target and re-run the full project checks:

```bash
git fetch origin
git switch main
git pull --ff-only origin main
lake build
python3 scripts/check_migration_sorries.py --certify
```

Do not merge this scaffold branch into `main`; transplant downstream work only
after the official migration has been certified.
