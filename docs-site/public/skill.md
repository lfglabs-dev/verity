# Verity Agent Skill

Use this skill when working in the Verity repository or docs. Verity is a Lean 4 framework for writing smart contracts that compile to EVM bytecode with machine-checked correctness proofs.

## First Principles

- Treat Lean files in `Contracts/<Name>/` as the source of truth.
- Keep specs, EDSL implementation, generated artifacts, and proofs aligned.
- Do not use `sorry`, `admit`, new `axiom`s, or unchecked assumptions to make proofs pass.
- Prefer existing Verity primitives and proof patterns before adding abstractions.
- Read `/llms.txt` first for the compact working model, then fetch `/llms-full.txt` when broader context is needed.

## Add A Contract

1. Scaffold with `python3 scripts/generate_contract.py <Name> --fields ... --functions ...` when the contract shape fits the generator.
2. Implement storage, specs, and EDSL functions under `Contracts/<Name>/`.
3. Register compiler integration following the existing contract examples.
4. Prove each public operation with the `_meets_spec` convention.
5. Run `lake build`.
6. If compiler behavior changes, run the relevant Foundry and property tests.

Primary docs:

- `/first-contract.md`
- `/guides/add-contract.md`
- `/edsl.md` (EDSL reference hub; subpages `/edsl/storage.md`, `/edsl/computation.md`, `/edsl/control-flow.md`, `/edsl/functions.md`, `/edsl/external-calls.md`)
- `/proof-techniques.md`
- `/guides/debugging-proofs.md`

## Port Solidity To Verity

1. Map Solidity state to Verity storage spaces before writing code.
2. Translate modifiers into explicit guard predicates and `require` checks.
3. Model external calls, precompiles, or oracle inputs as explicit trust-boundary assumptions unless the repo already has a verified surface.
4. Use `/guides/production-solidity-patterns.md` for ERC-7201 namespaces, proxy patterns, ECMs, events, and low-level mechanics.
5. Validate emitted trust, assumption, layout, and layout-compat reports.

Primary docs:

- `/guides/solidity-to-verity.md`
- `/guides/production-solidity-patterns.md`
- `/compiler.md`
- `/trust-model.md`

## Prove Specs

- The default theorem shape is `<operation>_meets_spec`.
- Most storage-only operations close by unfolding the operation, slot names, and spec, then using `simp`.
- For guard-protected operations, unfold `bind`, `Contract.run`, and `ContractResult.snd`, then pass the guard hypothesis to `simp`.
- For list or aggregate invariants, isolate helper lemmas near the proof instead of growing tactic scripts blindly.
- When stuck, inspect generated goals before changing the spec. A failing proof often means the spec, state shape, or revert path is underspecified.

## Audit Trust

- `lake build` verifies Lean proofs.
- Use compiler report flags for trust-sensitive changes: `--trust-report`, `--assumption-report`, `--layout-report`, and `--layout-compat-report`.
- Use deny flags to fail closed in CI or release builds. `--deny-unsafe` is the broad catch-all.
- Cross-check trust reports against `AXIOMS.md` and `/trust-model.md`.

## Useful Agent URLs

- `/llms.txt`: compact agent index.
- `/llms-full.txt`: all docs concatenated as Markdown.
- `/api/docs/_index`: JSON documentation index.
- `/api/docs/_all`: all docs concatenated through the API.
- `/<page>.md`: raw Markdown for any docs page.
- `/.well-known/llms.txt`: discovery alias.
- `/.well-known/llms-full.txt`: discovery alias.
- `/.well-known/skill.md`: discovery alias.
- `/.well-known/agent-skills`: skill discovery index.
