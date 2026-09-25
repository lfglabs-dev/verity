# Agent Guide for Verity

## Non-Negotiables

1. Keep `docs/TRUST_ASSUMPTIONS.md` and `docs/AXIOMS.md` synchronized with any semantic, trust or CI boundary change.
2. Never claim completion without evidence and passing checks.

## Core Commands

```bash
lake build          # Verify all Lean proofs
make check          # Run local CI-equivalent validation (no Lean build)
make test-python    # Run Python unit tests
make test-foundry   # Run Foundry differential tests
```

## Reference Docs

- Project overview and review order: [README.md](README.md)
- Contribution conventions: [CONTRIBUTING.md](CONTRIBUTING.md)
- Roadmap: [docs/ROADMAP.md](docs/ROADMAP.md)
- Solidity import: [docs/SOLIDITY_IMPORT.md](docs/SOLIDITY_IMPORT.md)
