#!/usr/bin/env python3
from __future__ import annotations

import fcntl
import json
import os
import re
import subprocess
import tempfile
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNNER_SCRIPT = ROOT / "scripts" / "install_self_hosted_runner.sh"
MAINTENANCE_SCRIPT = ROOT / "scripts" / "ci_host_maintenance.sh"
SETUP_FOUNDRY_ACTION = ROOT / ".github" / "actions" / "setup-foundry" / "action.yml"
VERIFY_WORKFLOW = ROOT / ".github" / "workflows" / "verify.yml"
DGX_SMOKE_WORKFLOW = ROOT / ".github" / "workflows" / "dgx-smoke.yml"


class CiInfraMaintenanceTests(unittest.TestCase):
    def test_runner_host_profiles_assign_healthier_build_host(self) -> None:
        text = RUNNER_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("88.99.4.254|healthy-build", text)
        self.assertIn('RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-build}"', text)
        self.assertIn('RUNNER_COUNT="${RUNNER_COUNT:-1}"', text)
        self.assertIn("ci-host-88-99-4-254", text)
        self.assertIn(
            '${RUNNER_LABELS_1:-verity,build,build-heavy,build-medium,hetzner,cpu-8,mem-64g}',
            text,
        )

    def test_runner_host_profiles_keep_overloaded_host_fastlane_only(self) -> None:
        text = RUNNER_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("95.216.244.60|mixed-8core", text)
        self.assertIn('RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-fastlane}"', text)
        self.assertIn("ci-host-95-216-244-60", text)
        self.assertIn("decommission_surplus_runners", text)
        self.assertIn('if [ "$index" -gt "$RUNNER_COUNT" ]; then', text)

    def test_runner_host_profiles_promote_dgx_to_fastlane_gpu(self) -> None:
        text = RUNNER_SCRIPT.read_text(encoding="utf-8")
        self.assertIn("spark-de79|dgx-spark", text)
        self.assertIn('RUNNER_PROFILE="${RUNNER_PROFILE_INPUT:-dgx-gpu}"', text)
        self.assertIn('RUNNER_ARCH="${RUNNER_ARCH_INPUT:-arm64}"', text)
        self.assertIn("verity,fastlane,dgx,dgx-spark,gpu,nvidia", text)
        self.assertIn("arm64-gb10", text)

    def test_verify_fastlane_jobs_are_arch_neutral(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        # Control-plane and Python-only jobs run on ephemeral GitHub-hosted
        # ubuntu-latest runners so they never serialize behind a single
        # self-hosted fastlane runner or expire in queue.
        self.assertNotIn(
            "runs-on: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]", text
        )
        for job in ("closed-pr-cleanup", "changes", "checks", "timeout-watchdog", "failure-hints", "ci-gate"):
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            self.assertIn(
                "runs-on: ubuntu-latest",
                match.group("body"),
                job,
            )

    def test_dgx_smoke_workflow_is_manual_only_and_gpu_routed(self) -> None:
        text = DGX_SMOKE_WORKFLOW.read_text(encoding="utf-8")
        self.assertIn("workflow_dispatch:", text)
        self.assertNotIn("pull_request:", text)
        self.assertIn("runs-on: [self-hosted, linux, ARM64, dgx-spark, gpu]", text)
        self.assertIn("nvidia-smi", text)

    def test_daily_host_maintenance_prunes_ci_disk_journald_and_docker(self) -> None:
        text = MAINTENANCE_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('CACHE_ROOT="${CACHE_ROOT:-/srv/verity-ci-cache}"', text)
        self.assertIn('prune_tree "$CACHE_ROOT/lake-build"', text)
        self.assertIn('prune_tree "$CACHE_ROOT/compiler-ccache"', text)
        self.assertIn('journalctl --vacuum-time="$JOURNAL_VACUUM_TIME"', text)
        self.assertIn('journalctl --vacuum-size="$JOURNAL_VACUUM_SIZE"', text)
        self.assertIn('docker image prune -af --filter "$DOCKER_PRUNE_FILTER"', text)
        # Daily, not weekly: the weekly run executed hours before the
        # 2026-07-12 disk-full incident and pruned nothing.
        self.assertIn("OnCalendar=*-*-* 04:30:00", text)
        self.assertNotIn("OnCalendar=Sun *-*-* 04:30:00", text)
        self.assertIn("verity-ci-host-maintenance.timer", text)

    def test_host_maintenance_bounds_lake_packages_cache(self) -> None:
        text = MAINTENANCE_SCRIPT.read_text(encoding="utf-8")
        self.assertIn('cap_tree_entries "$CACHE_ROOT/lake-packages"', text)
        self.assertIn('evict_until_free "$CACHE_ROOT/lake-packages"', text)
        self.assertIn('LAKE_PACKAGES_MAX_ENTRIES="${LAKE_PACKAGES_MAX_ENTRIES:-20}"', text)
        self.assertIn('MIN_FREE_GB="${MIN_FREE_GB:-100}"', text)
        self.assertIn('cap_tree_entries "$CACHE_ROOT/lake-build"', text)
        self.assertIn('evict_until_free "$CACHE_ROOT/lake-build"', text)
        self.assertIn('prune_tree "$CACHE_ROOT/elan"', text)
        # Root's daily run must not create root-owned lock files that the
        # runner user then cannot open: cache passes run as the cache owner.
        self.assertIn('runuser -u "$owner" -- "$@"', text)
        self.assertIn('as_cache_owner env CACHE_ROOT="$CACHE_ROOT" "$(readlink -f "$0")" caches', text)
        self.assertNotIn('  require_root\n  prune_caches', text)
        # In-use protection: recently attached entries are never deleted,
        # and the mount path refreshes the entry mtime on attach.
        self.assertIn('MIN_ENTRY_AGE_HOURS="${MIN_ENTRY_AGE_HOURS:-12}"', text)
        self.assertIn('LAKE_BUILD_MAX_ENTRIES="${LAKE_BUILD_MAX_ENTRIES:-12}"', text)
        self.assertIn('ELAN_MAX_AGE_DAYS="${ELAN_MAX_AGE_DAYS:-7}"', text)
        self.assertIn("entry_is_recent", text)
        persistence = (MAINTENANCE_SCRIPT.parent / "ci_local_persistence.sh").read_text(
            encoding="utf-8"
        )
        self.assertIn('touch "$primary_dir"', persistence)

    def _age(self, path: Path, hours: float) -> None:
        stamp = time.time() - hours * 3600
        os.utime(path, (stamp, stamp))

    def test_cache_pruning_spares_attached_entries(self) -> None:
        """Run the real pruning pass on a scratch cache root.

        Stale entries go; an entry attached by a running job (fresh mtime,
        however old its contents) survives every pass, including elan.
        """
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cache"
            entries = {}
            for tree in ("lake-build", "lake-packages", "elan", "compiler-ccache"):
                for name, hours in (("stale", 30 * 24), ("attached", 0.1)):
                    entry = root / tree / name
                    (entry / "payload").mkdir(parents=True)
                    self._age(entry / "payload", 30 * 24)
                    self._age(entry, hours)
                    entries[(tree, name)] = entry
            # More lake-build entries than the cap, all past the lease window
            # but inside the age limit: only the newest LAKE_BUILD_MAX_ENTRIES stay.
            for i in range(5):
                entry = root / "lake-build" / f"capped-{i}"
                entry.mkdir()
                self._age(entry, 24 + i)
            env = dict(os.environ, CACHE_ROOT=str(root), LAKE_BUILD_MAX_ENTRIES="3",
                       MIN_FREE_GB="0")
            subprocess.run(["bash", str(MAINTENANCE_SCRIPT), "caches"], check=True, env=env,
                           capture_output=True, text=True)
            for (tree, name), entry in entries.items():
                if name == "stale":
                    self.assertFalse(entry.exists(), entry)
                else:
                    self.assertTrue(entry.exists(), entry)
            kept = sorted(p.name for p in (root / "lake-build").iterdir())
            self.assertEqual(kept, ["attached", "capped-0", "capped-1"])

    def test_mount_leases_primary_and_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "lake-build"
            fallback = root / "main"
            (fallback / "lib").mkdir(parents=True)
            (fallback / "lib" / "Mod.olean").write_text("olean")
            self._age(fallback / "lib", 30 * 24)
            self._age(fallback, 30 * 24)
            work = Path(tmp) / "work"
            work.mkdir()
            subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "mount",
                            "--root", str(root), "--key", "pr", "--path", ".lake/build",
                            "--fallback-key", "main"], check=True, cwd=work,
                           capture_output=True, text=True)
            self.assertEqual((work / ".lake/build/lib/Mod.olean").read_text(), "olean")
            for entry in (root / "pr", fallback):
                self.assertLess(time.time() - entry.stat().st_mtime, 600, entry)

    def _lock(self, cache_root: Path, tree: str, entry: str):
        """Hold an entry lock the way an attaching job does (shared protocol)."""
        lock = cache_root / ".locks" / f"{tree}__{entry}.lock"
        lock.parent.mkdir(parents=True, exist_ok=True)
        handle = open(lock, "w")
        fcntl.flock(handle, fcntl.LOCK_EX)
        return handle

    def test_locked_entries_survive_every_deletion_path(self) -> None:
        """A stale entry whose lock is held is in use: no pass may delete it."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cache"
            for tree in ("lake-build", "lake-packages", "elan", "compiler-ccache"):
                entry = root / tree / "busy"
                entry.mkdir(parents=True)
                self._age(entry, 30 * 24)
            (root / "artifacts").mkdir()
            handles = [self._lock(root, tree, "busy")
                       for tree in ("lake-build", "lake-packages", "elan", "compiler-ccache")]
            try:
                # Huge MIN_FREE_GB forces low-space eviction to run for real.
                env = dict(os.environ, CACHE_ROOT=str(root), MIN_FREE_GB="999999999",
                           LAKE_BUILD_MAX_ENTRIES="0", LAKE_PACKAGES_MAX_ENTRIES="0",
                           VERITY_CI_ARTIFACT_ROOT=str(root / "artifacts"))
                subprocess.run(["bash", str(MAINTENANCE_SCRIPT), "caches"], check=True, env=env,
                               capture_output=True, text=True)
                subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "cleanup",
                                "--cache-max-age-hours", "1"], check=True, env=env,
                               capture_output=True, text=True)
                for tree in ("lake-build", "lake-packages", "elan", "compiler-ccache"):
                    self.assertTrue((root / tree / "busy").exists(), tree)
            finally:
                for handle in handles:
                    handle.close()
            # Released: the same passes now delete the stale entries.
            subprocess.run(["bash", str(MAINTENANCE_SCRIPT), "caches"], check=True, env=env,
                           capture_output=True, text=True)
            for tree in ("lake-build", "lake-packages", "elan"):
                self.assertFalse((root / tree / "busy").exists(), tree)
            subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "cleanup",
                            "--cache-max-age-hours", "1"], check=True, env=env,
                           capture_output=True, text=True)
            self.assertFalse((root / "compiler-ccache" / "busy").exists())

    def test_mount_waits_for_an_entry_being_deleted(self) -> None:
        """Attach serializes on the entry lock held by a deletion in progress."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cache"
            (root / "lake-build").mkdir(parents=True)
            work = Path(tmp) / "work"
            work.mkdir()
            handle = self._lock(root, "lake-build", "pr")
            try:
                result = subprocess.run(
                    ["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "mount",
                     "--root", str(root / "lake-build"), "--key", "pr", "--path", ".lake/build"],
                    cwd=work, env=dict(os.environ, MOUNT_LOCK_TIMEOUT="1"),
                    capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("timed out waiting for cache lock", result.stderr)
            finally:
                handle.close()

    def test_mount_seeds_atomically_over_a_torn_copy(self) -> None:
        """A copy killed mid-way leaves only a .seeding dir, never a partial entry."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cache" / "lake-build"
            (root / "main" / "lib").mkdir(parents=True)
            (root / "main" / "lib" / "Mod.olean").write_text("olean")
            torn = root / "pr.seeding"
            (torn / "lib").mkdir(parents=True)
            (torn / "lib" / "Partial.olean").write_text("trunc")
            work = Path(tmp) / "work"
            work.mkdir()
            subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "mount",
                            "--root", str(root), "--key", "pr", "--path", ".lake/build",
                            "--fallback-key", "main"], check=True, cwd=work,
                           capture_output=True, text=True)
            self.assertEqual(sorted(p.name for p in (root / "pr" / "lib").iterdir()), ["Mod.olean"])
            self.assertFalse(torn.exists())

    def test_cap_never_evicts_main_fallbacks(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "cache"
            tree = root / "lake-build"
            for name, hours in (("verify-build-ref-main-x", 48), ("pr-1", 24), ("pr-2", 25)):
                (tree / name).mkdir(parents=True)
                self._age(tree / name, hours)
            env = dict(os.environ, CACHE_ROOT=str(root), LAKE_BUILD_MAX_ENTRIES="1", MIN_FREE_GB="0")
            subprocess.run(["bash", str(MAINTENANCE_SCRIPT), "caches"], check=True, env=env,
                           capture_output=True, text=True)
            self.assertEqual(sorted(p.name for p in tree.iterdir()), ["pr-1", "verify-build-ref-main-x"])

    def _persistence(self, *args, env):
        return subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), *args],
                              env=env, capture_output=True, text=True)

    def test_artifact_hub_hands_artifacts_across_hosts(self) -> None:
        """Host A publishes, host B (different local store) fetches via the hub."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            hub, store_a, store_b = tmp / "hub", tmp / "a", tmp / "b"
            hub.mkdir()
            work_a, work_b = tmp / "work-a", tmp / "work-b"
            work_a.mkdir()
            work_b.mkdir()
            payload = work_a / "lean-workspace-build.tar.zst"
            subprocess.run(["tar", "-I", "zstd", "-cf", str(payload), "-C", str(ROOT), "README.md"],
                           check=True)
            out = tmp / "github_output"
            base = dict(os.environ, VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                        VERITY_CI_HUB_DIR=str(hub), GITHUB_OUTPUT=str(out))
            r = self._persistence("publish", "--run-id", "7", "--name", "lean-workspace-build",
                                  "--path", str(payload),
                                  env=dict(base, VERITY_CI_ARTIFACT_ROOT=str(store_a)))
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertIn("hub=true", out.read_text())
            self.assertTrue((hub / "7" / "lean-workspace-build" / ".ready").exists())
            r = subprocess.run(["bash", str(ROOT / "scripts" / "ci_local_persistence.sh"), "fetch",
                                "--run-id", "7", "--name", "lean-workspace-build"],
                               cwd=work_b, env=dict(base, VERITY_CI_ARTIFACT_ROOT=str(store_b)),
                               capture_output=True, text=True)
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("from the artifact hub", r.stdout)
            self.assertTrue((work_b / "README.md").exists())

    def test_artifact_hub_republish_replaces_stale_content(self) -> None:
        """A re-run's publish drops files and the .ready of the earlier attempt first."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            hub = tmp / "hub"
            stale = hub / "7" / "x"
            stale.mkdir(parents=True)
            (stale / "old.tar").write_text("attempt 1")
            (stale / ".ready").write_text("")
            new = tmp / "x.tar"
            new.write_text("attempt 2")
            r = self._persistence("publish", "--run-id", "7", "--name", "x", "--path", str(new),
                                  env=dict(os.environ, VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                                           VERITY_CI_HUB_DIR=str(hub),
                                           VERITY_CI_ARTIFACT_ROOT=str(tmp / "store")))
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(sorted(p.name for p in stale.iterdir()), [".ready", "x.tar"])

    def test_artifact_hub_ignores_incomplete_artifacts(self) -> None:
        """No .ready on the hub (producer still uploading): fall back to GitHub."""
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "hub" / "7" / "x").mkdir(parents=True)
            (tmp / "hub" / "7" / "x" / "x.tar").write_text("partial")
            r = self._persistence("fetch", "--run-id", "7", "--name", "x",
                                  env=dict(os.environ, VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                                           VERITY_CI_HUB_DIR=str(tmp / "hub"),
                                           VERITY_CI_ARTIFACT_ROOT=str(tmp / "store")))
            self.assertEqual(r.returncode, 2)
            self.assertFalse((tmp / "store" / "7" / "x").exists())

    def test_artifact_hub_rejects_marker_without_payload(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            (tmp / "hub" / "7" / "x").mkdir(parents=True)
            (tmp / "hub" / "7" / "x" / ".ready").write_text("")
            r = self._persistence("fetch", "--run-id", "7", "--name", "x",
                                  env=dict(os.environ, VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                                           VERITY_CI_HUB_DIR=str(tmp / "hub"),
                                           VERITY_CI_ARTIFACT_ROOT=str(tmp / "cache" / "artifacts")))
            self.assertEqual(r.returncode, 2)
            self.assertFalse((tmp / "cache" / "artifacts" / "7" / "x").exists())
            self.assertNotIn("::error::", r.stdout)

    def test_no_hub_keeps_github_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            r = self._persistence("fetch", "--run-id", "7", "--name", "x",
                                  env=dict(os.environ, VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                                           VERITY_CI_ARTIFACT_ROOT=str(tmp / "store")))
            self.assertEqual(r.returncode, 2)

    def test_ephemeral_heavy_build_jobs_use_all_vm_cores(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        def job_body(job: str) -> str:
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            return match.group("body")

        for job in (
            "build-audits",
            "build-compiler-binaries",
            "compiler-audits",
            "compiler-regressions",
            "lean-profile",
        ):
            body = job_body(job)
            # lean.ci sizes and grows these VMs; Lean must use the cores it gets.
            self.assertNotIn("LEAN_NUM_THREADS:", body, job)
        # `build` is the exception: a burst VM (more vCPUs than its 8-vCPU label,
        # memory scaled by half the ratio) ran one Lean per vCPU and hit ENOMEM,
        # so its Lake parallelism stays at the label's 8.
        self.assertRegex(job_body("build"), r"\n    env:\n(?:      #.*\n)*      LEAN_NUM_THREADS: 8\n")
        # No step may set it again (step env or $GITHUB_ENV).
        self.assertEqual(len(re.findall(r"^\s+LEAN_NUM_THREADS:", job_body("build"), re.M)), 1)
        self.assertNotIn("LEAN_NUM_THREADS=", job_body("build"))
        for job in ("build", "build-compiler-binaries", "compiler-regressions", "lean-profile"):
            self.assertIn("runs-on: lean-", job_body(job), job)

        routed_runs_on = "runs-on: ${{ fromJSON(needs.route.outputs.runs_on) }}"
        routed = (
            "build-audits",
            "import-mutations",
            "compiler-audits",
            "foundry-gas-calibration",
            "foundry",
            "foundry-patched",
            "foundry-multi-seed",
        )
        for job in routed:
            body = job_body(job)
            self.assertIn(routed_runs_on, body, job)
            self.assertRegex(body, r"(?m)^    needs: \[changes, route(, [a-z-]+)*\]$", job)
        # Only the routed jobs may land on build-medium, and only through `route`.
        self.assertEqual(text.count(routed_runs_on), len(routed))
        self.assertNotIn("runs-on: [self-hosted, linux, x64, verity, build, build-medium]", text)

        route = job_body("route")
        self.assertIn("runs-on: ubuntu-latest", route)
        self.assertIn("    permissions:\n      actions: read\n", route)
        self.assertIn("ROUTE_POOLS: ${{ vars.ROUTE_POOLS }}\n", route)
        self.assertIn("pool: ${{ steps.route.outputs.pool }}\n", route)
        # The built-in pool list (used when ROUTE_POOLS is unset or invalid)
        # matches the previous fixed routing: build-medium below 6 queued, then lean-8.
        default = re.search(r"(?m)^  VERIFY_ROUTE_POOLS_DEFAULT: '(.*)'$", text)
        self.assertIsNotNone(default)
        self.assertEqual(
            json.loads(default.group(1)),
            [
                {
                    "name": "build-medium",
                    "labels": ["self-hosted", "linux", "x64", "verity", "build", "build-medium"],
                    "max_queue": 6,
                },
                {"name": "lean-8", "labels": ["lean-8vcpu-ubuntu-2604"]},
            ],
        )
        self.assertRegex(job_body("ci-gate"), r"(?m)^    needs: \[changes, route, ")

        # build-medium keeps main's per-host limits; lean.ci keeps the VM defaults.
        self.assertIn(
            "      - name: Cap Lean threads on build-medium\n"
            "        if: needs.route.outputs.on_lean != 'true'\n"
            "        run: echo \"LEAN_NUM_THREADS=4\" >> \"$GITHUB_ENV\"\n",
            job_body("build-audits"),
        )
        self.assertIn(
            "max-parallel: ${{ needs.route.outputs.on_lean == 'true' && 4 || 2 }}",
            job_body("foundry"),
        )
        self.assertIn(
            "max-parallel: ${{ needs.route.outputs.on_lean == 'true' && 7 || 1 }}",
            job_body("foundry-multi-seed"),
        )
        for job in ("import-mutations", "foundry-gas-calibration", "foundry-patched"):
            self.assertNotIn("max-parallel:", job_body(job), job)

    def test_route_job_picks_pool_from_queue_depth(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        match = re.search(
            r"^        id: route\n(?:        .*\n)*?        run: \|\n(?P<run>(?:          .*\n|\n)+)",
            text,
            re.M,
        )
        self.assertIsNotNone(match)
        script = "\n".join(line[10:] for line in match.group("run").splitlines())
        default = re.search(r"(?m)^  VERIFY_ROUTE_POOLS_DEFAULT: '(.*)'$", text).group(1)
        medium = '["self-hosted","linux","x64","verity","build","build-medium"]'
        lean = '["lean-8vcpu-ubuntu-2604"]'
        lean4 = '["lean-4vcpu-ubuntu-2604"]'
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            fake_gh = tmp / "gh"
            # The jobs endpoint prints FAKE_LABELS (the labels of each queued job,
            # one JSON array per line, as `--jq` would); FAKE_FAIL=1 fails the API.
            fake_gh.write_text(
                "#!/usr/bin/env bash\n"
                '[ "${FAKE_FAIL:-0}" = 1 ] && exit 1\n'
                'case "$*" in *"/jobs"*) printf \'%s\' "$FAKE_LABELS" ;; *status=queued*) echo 11 ;; esac\n',
                encoding="utf-8",
            )
            fake_gh.chmod(0o755)

            def route(
                mode: str, queued: list[str], fail: bool = False, pools: str = ""
            ) -> tuple[dict[str, str], str]:
                out = tmp / "out"
                out.write_text("", encoding="utf-8")
                proc = subprocess.run(
                    ["bash", "-c", script],
                    check=True,
                    capture_output=True,
                    text=True,
                    env=dict(
                        os.environ,
                        PATH=f"{tmp}:{os.environ['PATH']}",
                        GITHUB_OUTPUT=str(out),
                        GITHUB_STEP_SUMMARY=str(tmp / "summary"),
                        REPO="o/r",
                        RUNNER_ROUTE=mode,
                        ROUTE_POOLS=pools,
                        VERIFY_ROUTE_POOLS_DEFAULT=default,
                        FAKE_LABELS="".join(f"{labels}\n" for labels in queued),
                        FAKE_FAIL="1" if fail else "0",
                    ),
                )
                return dict(line.split("=", 1) for line in out.read_text().splitlines()), proc.stdout

            def chosen(pool: str, runs_on: str) -> dict[str, str]:
                on_lean = "false" if "build-medium" in runs_on else "true"
                return {"runs_on": runs_on, "on_lean": on_lean, "pool": pool}

            # Built-in default: build-medium below 6 queued, then lean-8.
            self.assertEqual(route("auto", [medium] * 5 + [lean] * 9)[0], chosen("build-medium", medium))
            self.assertEqual(route("auto", [medium] * 6)[0], chosen("lean-8", lean))
            self.assertEqual(route("auto", [medium] * 6, fail=True)[0], chosen("build-medium", medium))
            summary = (tmp / "summary").read_text(encoding="utf-8")
            self.assertIn("GitHub API error; falling back to the first pool", summary)
            # Forced pools; `lean` is the old name of lean-8.
            self.assertEqual(route("lean", [])[0], chosen("lean-8", lean))
            self.assertEqual(route("lean-8", [])[0], chosen("lean-8", lean))
            self.assertEqual(route("build-medium", [medium] * 50)[0], chosen("build-medium", medium))
            outputs, stdout = route("nope", [medium] * 6)
            self.assertEqual(outputs, chosen("lean-8", lean))
            self.assertIn("::warning::runner route: unknown pool 'nope'", stdout)
            # A three-pool ROUTE_POOLS variable; a pool counts jobs carrying all its labels.
            three = json.dumps(
                [
                    {"name": "build-medium", "labels": json.loads(medium), "max_queue": 2},
                    {"name": "lean-4", "labels": json.loads(lean4), "max_queue": 1},
                    {"name": "lean-8", "labels": json.loads(lean)},
                ]
            )
            self.assertEqual(route("auto", [medium], pools=three)[0], chosen("build-medium", medium))
            self.assertEqual(route("auto", [medium] * 2, pools=three)[0], chosen("lean-4", lean4))
            self.assertEqual(
                route("auto", [medium] * 2 + [lean4], pools=three)[0], chosen("lean-8", lean)
            )
            self.assertEqual(route("auto", ['["build-medium"]'] * 9, pools=three)[0], chosen("build-medium", medium))
            summary = (tmp / "summary").read_text(encoding="utf-8")
            self.assertIn("Pools from the ROUTE_POOLS repository variable", summary)
            self.assertIn("`lean-4` " + lean4 + ": 0 / 1", summary)
            # Invalid variables fall back to the default with a warning; unset is silent.
            for bad in ('[{"name":"x"', "[]", '[{"name":"x","labels":[]}]', '[{"name":"x","labels":["a"],"max_queue":"6"}]'):
                outputs, stdout = route("auto", [medium] * 6, pools=bad)
                self.assertEqual(outputs, chosen("lean-8", lean), bad)
                self.assertIn("ROUTE_POOLS is not a valid pool list", stdout, bad)
            self.assertNotIn("::warning::", route("auto", [])[1])

    def test_ephemeral_persistence_falls_back_when_srv_unavailable(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            target = tmp / "ccache"
            env = dict(
                os.environ,
                VERITY_CI_HUB_ENV=str(tmp / "absent.env"),
                RUNNER_TEMP=str(tmp / "runner-temp"),
            )
            env.pop("VERITY_CI_ARTIFACT_ROOT", None)
            r = self._persistence(
                "mount",
                "--root",
                "/proc/nonexistent-verity-ci-cache/compiler-ccache",
                "--key",
                "k1",
                "--path",
                str(target),
                env=env,
            )
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertTrue(target.is_symlink())
            self.assertIn("runner-temp", str(target.resolve()))

    def _extract_setup_foundry_step_run(self, step_id: str) -> str:
        text = SETUP_FOUNDRY_ACTION.read_text(encoding="utf-8")
        match = re.search(
            rf"^\s*-\s+name:.*?\n\s+id:\s+{re.escape(step_id)}\n\s+shell:\s+bash\n\s+run:\s+\|\n(?P<run>(?:        .*\n)+)",
            text,
            re.M,
        )
        self.assertIsNotNone(match, step_id)
        return "\n".join(line[8:] for line in match.group("run").splitlines())

    def _write_fake_foundry_tool(self, bin_dir: Path, name: str, *, works: bool = True) -> None:
        tool = bin_dir / name
        body = "#!/usr/bin/env bash\n" + (
            f'echo "{name} 1.5.0"\n' if works else "exit 1\n"
        )
        tool.write_text(body, encoding="utf-8")
        tool.chmod(0o755)

    def test_setup_foundry_reinstalls_when_cached_or_preinstalled_tools_fail_validation(self) -> None:
        text = SETUP_FOUNDRY_ACTION.read_text(encoding="utf-8")
        self.assertIn(
            "        path: |\n"
            "          ~/.foundry/bin\n"
            "          ~/.foundry/versions\n"
            "        key: foundry-v1.5.0-linux-amd64-v2",
            text,
        )
        self.assertIn(
            "- name: Install Foundry\n      if: steps.validate-foundry.outputs.valid != 'true'",
            text,
        )
        self.assertIn(
            "- name: Install Foundry fallback (retry on transient download errors)\n"
            "      if: steps.validate-foundry.outputs.valid != 'true' && steps.install_foundry_primary.outcome != 'success'",
            text,
        )
        self.assertNotIn("steps.cache-foundry.outputs.cache-hit != 'true'", text)

        preinstalled_script = self._extract_setup_foundry_step_run("preinstalled-foundry")
        validate_script = self._extract_setup_foundry_step_run("validate-foundry")

        for step_id, script, key in (
            ("preinstalled-foundry", preinstalled_script, "installed"),
            ("validate-foundry", validate_script, "valid"),
        ):
            with tempfile.TemporaryDirectory() as tmp:
                home = Path(tmp) / "home"
                bin_dir = home / ".foundry" / "bin"
                bin_dir.mkdir(parents=True)
                output = Path(tmp) / "github_output"

                def run_step() -> str:
                    output.write_text("", encoding="utf-8")
                    subprocess.run(
                        ["bash", "-euo", "pipefail", "-c", script],
                        check=True,
                        env=dict(os.environ, HOME=str(home), GITHUB_OUTPUT=str(output)),
                        capture_output=True,
                        text=True,
                    )
                    return output.read_text(encoding="utf-8").strip()

                self.assertEqual(run_step(), f"{key}=false", step_id)

                for name in ("forge", "anvil"):
                    self._write_fake_foundry_tool(bin_dir, name)
                self.assertEqual(run_step(), f"{key}=false", step_id)

                (bin_dir / "cast").symlink_to(home / ".foundry" / "versions" / "missing" / "cast")
                self.assertEqual(run_step(), f"{key}=false", step_id)
                (bin_dir / "cast").unlink()

                self._write_fake_foundry_tool(bin_dir, "cast", works=False)
                self.assertEqual(run_step(), f"{key}=false", step_id)

                self._write_fake_foundry_tool(bin_dir, "cast", works=True)
                self.assertEqual(run_step(), f"{key}=true", step_id)

                self._write_fake_foundry_tool(bin_dir, "forge", works=False)
                self.assertEqual(run_step(), f"{key}=false", step_id)


if __name__ == "__main__":
    unittest.main()
