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

- `normal`: OCR runs with the current pilot bounds (`--concurrency 3`, `--timeout 20`, PR background capped at 1200 characters). This is used for non-Lean supported changes and small Lean diffs of at most 1 Lean file and 300 supported changed lines.
- `bounded-lean`: OCR runs with stricter bounds (`--concurrency 1`, `--timeout 12`, PR background capped at 800 characters). This is used for medium Lean diffs that are above the small threshold but below the large guard.
- `guarded-large-lean`: OCR does not run. The workflow posts a deterministic advisory comment with changed-file counts, largest files, and thresholds. This triggers for at least 3 changed Lean files or more than 800 supported changed lines.
- `skipped`: OCR does not run because no changed files match the OCR include rules.

The guarded mode is intentional: during the pilot, a 3-file Lean PR consumed about 1.25M tokens, made 121 tool calls, and still ended as `completed_with_errors`. Large Lean changes need Codex Review and human proof review rather than an unbounded OCR attempt.

Deduplication includes the commit, rules hash, reviewer version, router version, and routing mode. Retryable OCR statuses such as `completed_with_errors` do not write the success dedup tag, while deterministic guarded/skipped routing posts use a stable success tag to avoid repeated `/ocr review` spam for the same commit and router policy.

Promote beyond pilot only after comparing OCR vs Codex on real PRs for true positives, false positives, latency, and cost.
