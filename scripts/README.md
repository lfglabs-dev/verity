# Scripts Quickstart

Use this file for day-to-day operation. Each script's docstring describes what it checks.

## High-signal commands

```bash
# Local CI-equivalent subset
make check

# Regenerate the committed derived artifacts
make refresh-status

# Print current repository counts (tests, theorems, coverage); ARGS=--json for JSON
make status

# Run Python unit tests
make test-python

# Profile a CI-equivalent command and write JSON/log artifacts
python3 scripts/profile_ci_resources.py --name check --output-dir artifacts/ci-profile -- make check

# Run Foundry differential tests
make test-foundry

# Rebase the current PR branch onto origin/main, resolving generated files and
# append-only lists, regenerating at the end (never pushes; --json for JSON)
python3 scripts/rebase_pr_onto_main.py
```

## CI host operations

```bash
# On 88.99.4.254, install one build runner on the healthier CI host.
sudo RUNNER_HOST_PROFILE=88.99.4.254 RUNNER_URL=https://github.com/<owner>/<repo> RUNNER_TOKEN=<token> \
  scripts/install_self_hosted_runner.sh

# On 95.216.244.60, keep only the fastlane runner and decommission surplus numbered runners.
sudo RUNNER_HOST_PROFILE=95.216.244.60 RUNNER_URL=https://github.com/<owner>/<repo> RUNNER_TOKEN=<token> \
  scripts/install_self_hosted_runner.sh

# On spark-de79, register one ARM64 GPU-only runner. Do not add Verity build labels.
sudo RUNNER_HOST_PROFILE=dgx-spark RUNNER_URL=https://github.com/<owner>/<repo> RUNNER_TOKEN=<token> \
  scripts/install_self_hosted_runner.sh

# Install daily cache, journald, and Docker image cleanup.
sudo scripts/ci_host_maintenance.sh install-systemd
```

## Sources of truth

- Verify workflow sync contract source: `scripts/verify_sync_spec_source.py`
- Generated verify workflow sync artifact: `scripts/verify_sync_spec.json`
- Unified verify workflow validator: `scripts/check_verify_sync.py`
- Docs workflow trigger contract: `scripts/check_docs_workflow_sync.py`
- Verification metrics: `scripts/verification_metrics.py` (`current_metrics()`, computed on demand; `make status` prints them; `scripts/generate_verification_status.py` writes the git-ignored `artifacts/verification_status.json`)
