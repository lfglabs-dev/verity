# OpenCodeReview pilot

This repository runs Alibaba OpenCodeReview as a **non-blocking first-pass reviewer**.

Current policy:

- OCR comments are advisory.
- Codex Review remains the merge/review gate for important PRs.
- The workflow uses `pull_request_target` and checks out trusted OCR scripts/rules from the default branch before checking out PR code.
- Fork PRs are skipped during the pilot so LLM credentials are never exposed to untrusted code.
- OCR runs on Thomas/Paloma-managed self-hosted runner label `paloma-ocr`.
- LLM credentials are GitHub Actions secrets: `OCR_LLM_URL` and `OCR_LLM_KEY`; model is `reviewer`; protocol is OpenAI-compatible.

Manual trigger on a PR:

```text
/ocr review
```

The workflow uses `.github/ocr/rules.json` for Verity-specific review focus and `.github/scripts/ocr-git-wrapper.sh` as a temporary compatibility shim for OpenCodeReview 1.7.5 on Git versions whose `git grep` does not support `--end-of-options`.

## Routing modes

Before installing or invoking OpenCodeReview, `.github/scripts/ocr-router.js` compares the PR head against the base branch and writes safe metrics to `$RUNNER_TEMP/ocr-metrics.json`.

- `no-supported`: OCR does not run because no changed files match the OCR include rules.
- `small-lean`: OCR runs with the current pilot bounds (`--concurrency 3`, `--timeout 20`, PR background capped at 1200 characters). This is used for Lean diffs of at most 1 Lean file and 300 supported changed lines.
- `medium-lean`: OCR runs with stricter bounds (`--concurrency 1`, `--timeout 12`, PR background capped at 800 characters). This is used for medium Lean diffs that are above the small threshold but below the large threshold.
- `large-lean-hotspots`: full-file OCR does not run. The trusted router parses diff hunks, builds a compact risk dossier, optionally asks a cheap/long-context scout model to rank dangerous packets, and posts bounded hotspot coverage. This triggers for at least 3 changed Lean files or more than 800 supported changed lines. If the diff exceeds the bounded packet budget, more than 12 Lean files or more than 2500 supported changed lines, or no safe packets can be produced, the same mode posts a concrete coverage report and checklist instead of a generic skip.
- `config-docs`: OCR runs with the current pilot bounds for supported non-Lean changes, including workflows, scripts, docs, trust/security surfaces, Solidity, Yul, Cairo, and config files.

Packetized Lean mode is intentionally partial. It checks deterministic signals first, including introduced `sorry`/`admit`/`axiom`/`unsafe`, changed imports, public declaration or theorem signature changes, trust-boundary documentation drift, and large deleted proof obligations. It then ranks hotspots such as `Compiler/Proofs/YulGeneration/**`, `Compiler/Proofs/**`, `Compiler/**`, `IRGeneration/**`, `Semantics/**`, trust docs, and public theorem statements.

For `large-lean-hotspots`, the scout is enabled by default and uses sandboxed.sh/OpenAI-compatible routing. Configuration knobs:

- `OCR_SCOUT_ENABLED`: optional, defaults to `true`; set to `false` to disable only the large Lean scout call.
- `OCR_SCOUT_LLM_URL`: optional; defaults to `OCR_LLM_URL` when the same sandboxed endpoint supports model selection.
- `OCR_SCOUT_LLM_KEY`: optional; defaults to `OCR_LLM_KEY`, then `OCR_LLM_TOKEN`, when the same sandboxed key can route both models.
- `OCR_SCOUT_LLM_MODEL`: optional; defaults to `MiniMax-M3`, the MiniMax hybrid long-context scout model listed in the sandboxed.sh provider catalog.
- `OCR_SCOUT_LENSES`: optional; comma-separated list of lens ids to run instead of the full set (unknown/empty values fall back to all lenses).

The router sends only a bounded JSON risk dossier to the scout model. The scout model is cheap triage only: it selects packet IDs, reasons, risk categories, questions for a stronger reviewer, and residual coverage. It never produces final review approval. If scout configuration is absent, disabled, malformed, rejected by the provider, or the call fails, the router records that state in metrics and falls back to deterministic ranking.

### Multi-lens scout

A single scout pass converges serially: on a real PR each pass surfaced exactly one new class of defect, so review took three cycles (checksum-manifest scoping → verification-replay independence → shallow-clone verification contract). Instead of one call, the router now runs one scout call **per lens in parallel** and **unions + de-duplicates** their packet selections, so a single review surfaces every defect class at once. Each lens reframes the same bounded dossier toward a distinct failure family; the lens set is data-driven (`LENSES` in `ocr-router.js`, subsettable via `OCR_SCOUT_LENSES`). The starting lenses are:

- `provenance` — data/artifact provenance and manifest scoping.
- `verification-independence` — whether a claimed-independent check actually reuses producer code or a shallow clone.
- `environment-determinism` — env/override/toolchain assumptions (e.g. NVCC/RUN_CPU flags, unpinned toolchains).
- `proof-soundness` — Lean vacuous/over-strong hypotheses, `sorry`/`admit`/`axiom`, unsound tactic shortcuts.

All lens calls reuse the same per-call `scoutTimeoutMs` (240s) and run concurrently, so wall-clock time stays bounded to a single scout timeout rather than N of them. A packet flagged by several lenses appears once, carrying every lens's finding (`scout_lenses`); the legacy single-value fields (`scout_reason`/`scout_risk_category`/`scout_question`) and the `<!-- paloma-ocr-review:… -->` dedup tag / verdict line / findings shape are preserved. If **some** lenses fail the union of the survivors is used (`partial_lens_failures` is recorded); only if **every** lens fails does the router fall back to deterministic ranking.

### Accumulating rubric

`.github/ocr/rubric.json` is a permanent, growing checklist of defect **classes** confirmed on past PRs (seeded with the three above). Every scout dossier embeds the rubric (`dossier.rubric`), and each lens also gets a lens-scoped `lens_rubric_focus` pointing it at the past defect classes it owns — so a class caught once is re-checked on every future review instead of being rediscovered serially. When a review confirms a **new** defect class, append it with the `appendRubricItem({ id, lens, title, check, origin })` helper in `ocr-router.js` (it de-dupes by `id`); that helper is also the wiring point for future automation. A missing/invalid rubric file is a soft failure — the scout still runs.

OpenCodeReview 1.7.5 is still invoked only for `small-lean`, `medium-lean`, and `config-docs` full-diff paths. The short-term bridge for `large-lean-hotspots` publishes scout/deterministic packet advisory comments and explicitly marks strong packet review as required but blocked on a safe OCR packet-window input mechanism. The posted comment lists the covered packets, packet budget, scout status, metrics, strong-review blocker, and residual risk. It must not be read as full review coverage or LGTM.

The hard guarded modes are fallback behavior only. During the pilot, a 3-file Lean PR consumed about 1.25M tokens, made 121 tool calls, and still ended as `completed_with_errors`; packetized review is meant to keep OCR useful without pretending it reviewed whole files.

Deduplication includes the commit, rules hash, reviewer version, router version, and routing mode. Retryable OCR statuses such as `completed_with_errors` do not write the success dedup tag, while deterministic `no-supported` and `large-lean-hotspots` routing posts use a stable success tag to avoid repeated `/ocr review` spam for the same commit and router policy.

Promote beyond pilot only after comparing OCR vs Codex on real PRs for true positives, false positives, latency, and cost.

## Large-Lean packet semantic review (2026-07-31)

Large Lean PRs (≥3 Lean files or >800 changed lines) previously stopped at
scout triage. The route now continues:

1. The multi-lens scout selects packets as before; the router writes an
   executable plan (`ocr-packet-plan.json`) grouping selected packets by file.
2. `ocr-packet-review.js` runs the real `ocr review` once per group, scoped by
   excluding the exact complement (every other changed supported file — `ocr`
   has no `--include` flag). ~10 min budget per group, at most 4 groups, one
   at a time; a group failure never discards another group's findings.
3. `post-ocr-review.js` publishes an **`OCR semantic review` check-run** that
   carries the honest meaning: `success` only when a semantic review covered
   the diff (full OCR, or all planned packet groups), `neutral` for
   triage-only/partial coverage, `failure` on errored runs. The pipeline job
   staying green only means the pipeline ran.
4. Scout inline markers now lead with a "question de triage (non-review)"
   caveat, stale markers from older heads are minimized as OUTDATED on the
   next successful post, and the summary's first line reports
   `covered/total` packet groups with uncovered groups listed unfolded.
5. Scout dossiers embed a bounded node-side outline of each packet's file
   (declarations + `sorry`/`axiom`/`native_decide` markers). Full LSP
   diagnostics remain the packet reviewer's tools via its `lean_lsp` MCP
   session.

Kill switch: repo variable `OCR_PACKET_REVIEW_ENABLED=false`;
per-group budget: `OCR_PACKET_TIMEOUT_MINUTES` (default 10).
