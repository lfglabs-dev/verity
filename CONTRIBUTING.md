# Contributing to Verity

## Pull requests

Title with a category prefix (`[Layer 3]`, `[Trust Reduction]`,
`[Compiler Enhancement]`, `[Documentation]`, `[Infrastructure]`, …). The body
has a **Summary**, a **Test Plan** (what you ran), and **Related Issues**.
Issues use the templates in `.github/ISSUE_TEMPLATE/`.

Before opening a PR:

```sh
lake build        # every proof must check
make check        # repository checks, as in CI
make test-foundry # property and differential tests (uses vm.ffi)
```

A change to the trust boundary, an axiom, or CI updates
[docs/TRUST_ASSUMPTIONS.md](docs/TRUST_ASSUMPTIONS.md) and
[docs/AXIOMS.md](docs/AXIOMS.md) in the same PR.

To bring a PR branch up to date with main, run
`python3 scripts/rebase_pr_onto_main.py` on a clean branch that matches its
upstream. It rebases onto `origin/main`, takes main's side of generated files
(`artifacts/*.json`, `scripts/verify_sync_spec.json`) and regenerates them once
at the end, union-merges the append-only smoke lists and differential fixture
registries, drops old `chore: regenerate`
commits, and stops with the file list (exit 3) on any other conflict; rerun it
after resolving to resume. It never pushes: it prints the
`git push --force-with-lease` command to run.

## Proof hygiene

Enforced by CI; changing a rule means changing its script.

1. No `sorry` (`scripts/check_lean_hygiene.py` double-checks the build).
2. No new axiom without a same-commit entry in docs/AXIOMS.md
   (`scripts/check_axioms.py`).
3. `PrintAxioms.lean`, `scripts/VerityUnionAxioms.lean` and
   `artifacts/trust_surface_report.json` are generated, never committed:
   `make check` and CI write them (`scripts/generate_print_axioms.py`,
   `scripts/generate_trust_surface_report.py`); run the generators yourself
   before `lake build PrintAxioms` or `make axiom-report`. Repository counts (tests, theorems, lines) are computed
   on demand and never committed: `make status` prints them.
4. Proofs stay under 30 lines; over 50 needs an allowlist entry with a reason
   (`scripts/check_proof_length.py`).
5. No `native_decide` outside smoke tests, and no `#eval`/`#check`/`#print`
   in proof files.

## Adding an axiom

Avoid it: try to prove it, weaken the lemma, or refactor. If it is truly
needed, document it in docs/AXIOMS.md (statement, soundness justification, why
a proof is not feasible, risk, elimination path) and mark the declaration with
an `AXIOM:` doc comment pointing there.

## Adding a contract or intrinsic

- Write contracts with `verity_contract`; reusable facets are `verity_mixin`s
  that hosts `include`. `python3 scripts/generate_contract.py <Name>`
  scaffolds the files; `scripts/check_contract_structure.py` checks them.
- Refresh `test/property_manifest.json`
  (`python3 scripts/extract_property_manifest.py`) and the other derived
  artifacts (`make refresh-status`); counts are not committed.
- Intrinsics (`verity_intrinsic`) are consumer-owned opcode bindings; see
  [docs/INTRINSICS.md](docs/INTRINSICS.md).
- Solidity imports: see [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md) for
  what a new supported construct must ship with.

Layer 3 proof work starts from [Compiler/Proofs/README.md](Compiler/Proofs/README.md).
