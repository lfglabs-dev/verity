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

## Proof hygiene

Enforced by CI; changing a rule means changing its script.

1. No `sorry` (`scripts/check_lean_hygiene.py` double-checks the build).
2. No new axiom without a same-commit entry in docs/AXIOMS.md
   (`scripts/check_axioms.py`).
3. Regenerate `PrintAxioms.lean` (`scripts/generate_print_axioms.py`) and
   `artifacts/verification_status.json` (`make refresh-status`) when theorems
   or counts change.
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
  (`python3 scripts/extract_property_manifest.py`) and the counts
  (`make refresh-status`, `python3 scripts/update_doc_numbers.py`).
- Intrinsics (`verity_intrinsic`) are consumer-owned opcode bindings; see
  [docs/INTRINSICS.md](docs/INTRINSICS.md).
- Solidity imports: see [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md) for
  what a new supported construct must ship with.

Layer 3 proof work starts from [Compiler/Proofs/README.md](Compiler/Proofs/README.md).
