# Roadmap log

Chronological record of merges, closes, and cross-track decisions driven by the
roadmap agent. One line per event, newest last.

Format: `YYYY-MM-DD | <ref> | <track> | <one-sentence outcome>`

Tracks:
- **T1** — Fix CI
- **T2** — Prevent #2074/#2075-class regressions
- **T3** — Extend the proven fragment (issue #1723)
- **T4** — Refactor proofs into a lemma library
- **T5** — Prune the issue tracker
- **T6** — Faithful Solidity representation of Lido / ERC-4337 / Morpho

## Log

- 2026-07-02 | PR #2078 | T1 | Hardened `issue-intake-guard.yml` against
  script injection via `findings` output (env-var read instead of inline
  string interpolation).
- 2026-07-02 | PR (this) | T6 | Seeded `docs/parity/{lido,erc4337,morpho}.md`
  gap maps: Lido 44% ✅, ERC-4337 43% ✅, Morpho 47% ✅. Convergent top-3
  missing EDSL features across all three contracts: narrow uints
  (`uint128`/`uint64`/`uint48`), `abi.encode*` codec, first-class modifiers +
  inheritance.
- 2026-07-02 | PR (this) | T5 | Created `docs/roadmap/log.md` reporting
  infrastructure.
