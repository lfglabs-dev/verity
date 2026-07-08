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

Promote beyond pilot only after comparing OCR vs Codex on real PRs for true positives, false positives, latency, and cost.
