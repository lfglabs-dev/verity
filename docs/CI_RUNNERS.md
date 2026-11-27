# Verity CI Runner Architecture

This repository uses ephemeral `ubuntu-latest` and `lean.ci` runners for
standard CI workflows, plus official GitHub Actions runners installed directly
as `systemd` services on owned machines for specialized workloads (trusted GPU,
explicit ARM64 validation, OCR review, and optional host-pinned debugging). Do
not add ARC, GARM, Kubernetes, Docker runner wrappers, Nomad, or autoscaling
until the operational pain clearly justifies that extra layer.

## Current Topology

```text
GitHub Actions for lfglabs-dev/verity
  |
  |-- GitHub-hosted ephemeral runners
  |     role: fast control-plane/Python jobs, docs, issue intake, conformance
  |     runs-on: ubuntu-latest
  |
  |-- lean.ci ephemeral runners
  |     role: Lean proof builds, compiler binaries, profiling, turbo-lean
  |           cache checks; overflow pool for the routed jobs below
  |     runs-on: lean-4vcpu-ubuntu-2604, lean-8vcpu-ubuntu-2604,
  |              lean-16vcpu-ubuntu-2604
  |
  |-- build-medium self-hosted runners (3 hosts)
  |     role: routed jobs (audits, importer differential, import mutations,
  |           Foundry) while their queue is short
  |     labels: self-hosted, linux, x64, verity, build, build-medium
  |
  |-- dgx-spark-gpu-1
  |     host: spark-de79 over Tailscale
  |     role: trusted GPU jobs, explicit ARM64 Lean validation
  |     labels: self-hosted, linux, ARM64, verity, dgx, dgx-spark, gpu, nvidia
  |
  |-- paloma-ocr self-hosted runner
        role: OpenCodeReview pilot workflow
        labels: self-hosted, linux, x64, paloma-ocr
```

The workflows route by capability, not by hostname:

```yaml
runs-on: ubuntu-latest
runs-on: lean-4vcpu-ubuntu-2604
runs-on: lean-8vcpu-ubuntu-2604
runs-on: lean-16vcpu-ubuntu-2604
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
runs-on: [self-hosted, linux, x64, paloma-ocr]
```

Eight Verify jobs (`build-audits`, `importer-differential`, `import-mutations`,
`compiler-audits`, `foundry-gas-calibration`, `foundry`, `foundry-patched`,
`foundry-multi-seed`)
are routed at run time instead of naming a pool, each through its own router
output, for example:

```yaml
runs-on: ${{ fromJSON(needs.route-compiler.outputs.foundry_runs_on) }}
```

Two router jobs (`ubuntu-latest`, `actions: read`) run
`scripts/ci_route_pools.py` right before their groups fan out, so the choice
sees the runner load when the jobs are about to be created, not at the start
of the run: `route-build` needs `build` and routes `build-audits`,
`importer-differential`, then `import-mutations`; `route-compiler` needs
`build-compiler-binaries` and
routes `compiler-audits`, `foundry-gas-calibration`, `foundry`,
`foundry-patched`, `foundry-multi-seed`, in that order. (Run 45485073018
routed once at 20:51Z, before `build`; its 16 routed jobs were created 40-55
minutes later on the three build-medium hosts and 8 of them queued for over
40 minutes while lean-8 was idle.)

The script walks an ordered list of runner pools: the `ROUTE_POOLS`
repository variable, or `VERIFY_ROUTE_POOLS_DEFAULT` in `verify.yml` when the
variable is unset or invalid (an invalid value also emits a warning). Each
pool is `{"name", "labels", "slots"?, "max_queue"?}`. A job is on a pool when
its requested labels include all of the pool's labels; the script reads the
queued and in-progress jobs of every queued or in-progress run of the
repository. For each group in order, the first pool with room wins and the
last pool takes the rest:

- `slots` (the pool's runner count): room when the group's concurrent jobs
  fit in `slots` minus in-progress, queued, and already-routed jobs there. A
  matrix counts the shards that run at once on build-medium (`foundry` 2,
  `foundry-multi-seed` 1: their `max-parallel` there), its full size
  elsewhere. The workflow token cannot list self-hosted runners (that needs
  repository administration access), so the runner count is configuration:
  keep `slots` in sync with the build-medium hosts (today 3:
  `ashur-verity-build-medium-1`, `nippur-verity-build-1`,
  `old-agent-verity-build-medium-1`). An offline host, or jobs the router
  cannot see on those hosts, make it overestimate free capacity.
- `max_queue`: room while queued plus already-routed jobs stay below it.
- A pool with both needs both; one with neither always has room.

The default is `build-medium`
(`["self-hosted","linux","x64","verity","build","build-medium"]`, `slots` 3)
then `lean-8` (`["lean-8vcpu-ubuntu-2604"]`): build-medium first while it has
free runners for the whole group, lean-8 instead of queueing. A GitHub API
error routes every group to the first pool, except a group larger than the
first pool's `slots` (it could never fit), which takes the last pool. Adding a pool is a one-line
change to the variable, for example:

```json
[{"name":"build-medium","labels":["self-hosted","linux","x64","verity","build","build-medium"],"slots":3},
 {"name":"lean-4","labels":["lean-4vcpu-ubuntu-2604"],"max_queue":4},
 {"name":"lean-8","labels":["lean-8vcpu-ubuntu-2604"]}]
```

Manual dispatches can force a pool by name with the `runner_route` input
(`auto` by default; `lean` still means `lean-8`; an unknown name warns and
routes automatically); a forced pool applies to every group. Each router
outputs `<group>_runs_on` and `<group>_on_lean` (true when the chosen labels
do not include `build-medium`), with `-` in the job name written `_`. The
per-group choice and reason, and each pool's running, queued and routed
counts, are in the router job summary. On build-medium the routed jobs keep
main's per-host limits (`LEAN_NUM_THREADS=4` for `build-audits` and
`importer-differential`,
`max-parallel` 2 for `foundry` and 1 for `foundry-multi-seed`); on lean.ci
they use the whole VM and run every matrix entry at once. `ci-gate` needs
both routers, so a failed route (which skips the routed jobs) still fails
the gate.

Host labels such as `hz1`, `hz2`, and `ci-host-*` are inventory labels. Use
them only for temporary debugging or deliberate host pinning via
`runner-benchmark.yml` or `runner-lean-validation.yml`.

## Mindset

- Keep fast control-plane/Python jobs (`closed-pr-cleanup`, `changes`, `checks`,
  `timeout-watchdog`, `failure-hints`, `ci-gate`) on GitHub-hosted ephemeral
  `ubuntu-latest` runners so they run with unlimited concurrency and never
  serialize behind a single self-hosted host.
- Route Lean proof, compiler-binary, profiling, corpus coverage, and
  `turbo-lean` jobs onto ephemeral `lean.ci` runners (`lean-8vcpu-ubuntu-2604`
  for the build jobs, `lean-16vcpu-ubuntu-2604` for `solidity-import-coverage`,
  `lean-4vcpu-ubuntu-2604` for the turbo-lean cache check) so concurrent PRs
  do not serialize behind fixed self-hosted build pools. The audit,
  `importer-differential`, mutation and Foundry jobs go through `route-build` /
  `route-compiler`: build-medium while it has free runners,
  `lean-8vcpu-ubuntu-2604` once it is busy (`LEAN_NUM_THREADS=2` per worker
  on sharded `import-mutations` on either pool). On lean.ci, the
  Lake-building jobs (`build`, `build-audits`, `build-compiler-binaries`,
  `compiler-audits`, `compiler-regressions`, `importer-differential`,
  `lean-profile`) set `LEAN_NUM_THREADS` from the VM's memory with
  `scripts/ci_lean_threads.sh`: `clamp(floor(MemTotal / 3 GiB), 2,
  min(vCPUs, 8))`, 3 GiB being the 2.7 GiB peak of a heavy module plus
  headroom. lean.ci learns memory per label and can boot an 8-vCPU VM with
  ~11 GiB (3 threads there) or burst it to 32 vCPUs; one Lean/clang process
  per vCPU failed with ENOMEM (error code 12). lean.ci has no memory-only
  knob for a label (`memory_mib` exists only for Custom VMs); larger labels
  such as `boost-32vcpu-96gb` cost proportionally more vCPU-minutes and still
  learn their memory. Because lean.ci learns from recent peaks, fewer
  threads can shrink later VMs down to the floor of 2 (slower, not weaker):
  the step prints MemTotal and the chosen count. The lean.ci-side fix is to
  count exec/fork ENOMEM as an OOM so the label learns a bigger size. The
  full `import-mutations` run (24 shards, ~30 host-hours) needs ~12-14 h on
  the build-medium hosts when routed there.
  Ephemeral runners automatically fall back to GitHub Actions caches and
  `$RUNNER_TEMP` when `/srv/verity-ci-cache` is absent.
- Prefer one full Verity build runner per 8-core host when using self-hosted
  machines for manual benchmarks or validation. Lean jobs commonly use
  `LEAN_NUM_THREADS=8` on 8-core hosts; two such jobs on one 8-core host
  oversubscribe CPU, memory bandwidth, and the Lake cache.
- Add more build capacity by adding more machines first. Add more runner
  services on the same machine only after lowering per-job thread counts or
  proving the jobs are light enough.
- Use precise repo-specific labels on self-hosted runners so generic
  self-hosted jobs from other repositories cannot land on owned hosts by
  accident.
- Keep `/srv/verity-ci-cache` on a large disk and maintain it on self-hosted
  machines. Sticky Lake caches make local persistence fast, but stale
  `lake-build`, `compiler-ccache`, artifacts, Docker cache, and
  `/tmp/verity-main-test-*` directories must be pruned.
- Do not run untrusted public fork PRs on self-hosted machines. Self-hosted
  runners execute repository code on owned hosts.
- The DGX is especially sensitive. Keep it isolated to trusted GPU jobs and
  explicit ARM64 validation lanes (`dgx-smoke.yml`, `runner-benchmark.yml`,
  `runner-lean-validation.yml`).

## Adding A CPU Server

1. Create or reuse a dedicated runner user, runner root, and cache root.
2. Register exactly one build runner first.
3. Add host inventory labels.
4. Confirm the runner appears online and idle in GitHub.
5. Trigger `runner-benchmark.yml` or `runner-lean-validation.yml` with `workflow_dispatch`.

Use the repo script as root:

```bash
RUNNER_URL=https://github.com/lfglabs-dev/verity \
RUNNER_TOKEN=<registration-token> \
RUNNER_PROFILE=build \
RUNNER_COUNT=1 \
RUNNER_NAME_PREFIX=<short-hostname>-verity-build \
RUNNER_LABELS_1=verity,build,hetzner,<host-label>,cpu-8,mem-64g \
scripts/install_self_hosted_runner.sh
```

If the new host has more cores, prefer labels that describe reality, for
example `cpu-16,mem-128g`. Do not change workflow routing to those labels until
you intentionally want to require that capacity.

## Adding The DGX Spark

The DGX should be isolated from normal Verity CI. Register it for trusted GPU
workflows and explicit ARM64 Lean validation. At organization level, place it
in a restricted runner group instead of the default group.

```bash
RUNNER_URL=https://github.com/lfglabs-dev/verity \
RUNNER_TOKEN=<registration-token> \
RUNNER_PROFILE=dgx-gpu \
RUNNER_ARCH=arm64 \
RUNNER_COUNT=1 \
RUNNER_NAME_PREFIX=dgx-spark-gpu \
RUNNER_LABELS_1=verity,dgx,dgx-spark,gpu,nvidia,home,arm64-gb10 \
scripts/install_self_hosted_runner.sh
```

GPU and ARM64 Lean validation jobs should route explicitly:

```yaml
runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]
```

Do not let ordinary Verity `build` jobs use the DGX labels. Do not add the
`build` label to the DGX runner unless you have separately proven the ARM64
Lean build is reliable for required CI and intentionally want full Verity CI to
schedule there.

If DGX Lean validation becomes a regular lane, prefer adding a dedicated label
such as `dgx-lean` or `verity-arm64` instead of reusing `verity,build`. That
keeps x64 production proof CI separate from ARM64 validation and avoids routing
jobs with x64-only `solc`, Foundry, or artifact assumptions to the DGX.

The repository includes a manual-only smoke test:

```bash
gh workflow run dgx-smoke.yml
```

The repository also includes a manual-only runner benchmark workflow for
forcing real Verity tasks onto a chosen label set:

```bash
gh workflow run runner-benchmark.yml \
  -f task=checks \
  -f runner_labels_json='["self-hosted","linux","ARM64","dgx-spark","gpu"]'
```

Use it when adding a new host or comparing runner profiles. Keep it
`workflow_dispatch` only.

For deeper runner qualification, use the manual Lean validation workflow:

```bash
gh workflow run runner-lean-validation.yml \
  -f runner_labels_json='["self-hosted","linux","ARM64","dgx-spark","gpu"]' \
  -f include_compiler_core=true
```

This runs `make check`, full `lake build`, PrintAxioms/audit checks, and
compiler-core validation. On ARM64 it skips x64-only `solc` validation and runs
portable generated-Yul checks instead.

## Maintenance Expectations

Each self-hosted CI host should have the daily Verity maintenance timer
installed. It should:

- run `scripts/ci_local_persistence.sh cleanup`;
- prune stale Lake and compiler ccache buckets;
- remove stale Verity temp directories;
- vacuum journald by age and size;
- prune unused Docker image and builder cache.

The target health state is:

- all registered self-hosted runners online;
- no stale offline runner registrations;
- self-hosted cache hosts have enough free disk for sticky build caches and
  temporary host-pinned debugging;
- no more than one active full `LEAN_NUM_THREADS=8` build job per 8-core host.

Runner services should also have the Verity systemd stop hardening drop-in
installed:

```ini
[Service]
KillMode=control-group
SendSIGKILL=yes
TimeoutStopSec=90s
```

GitHub's generated service uses `KillMode=process`, which can leave cancelled
job children running. The repository installer writes this drop-in for future
runner installs.
