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

    def _lean_threads(self, mem_total_kib: int | None, nproc: int) -> tuple[subprocess.CompletedProcess, str]:
        with tempfile.TemporaryDirectory() as tmp:
            meminfo = Path(tmp) / "meminfo"
            lines = ["MemFree:         1000 kB"]
            if mem_total_kib is not None:
                lines.insert(0, f"MemTotal:       {mem_total_kib} kB")
            meminfo.write_text("\n".join(lines) + "\n", encoding="utf-8")
            github_env = Path(tmp) / "github_env"
            github_env.write_text("", encoding="utf-8")
            r = subprocess.run(
                ["bash", str(ROOT / "scripts" / "ci_lean_threads.sh")],
                env=dict(os.environ, CI_LEAN_THREADS_MEMINFO=str(meminfo),
                         CI_LEAN_THREADS_NPROC=str(nproc), GITHUB_ENV=str(github_env)),
                capture_output=True, text=True, check=False,
            )
            return r, github_env.read_text(encoding="utf-8")

    def test_lean_threads_follow_vm_memory(self) -> None:
        # MemTotal values printed by lean.ci `build` VMs on 2026-11-23.
        for mem_mib, nproc, expected in (
            (10941, 8, 3),    # 8 vCPUs / ~11 GiB: ENOMEM at 8 processes
            (14973, 24, 4),
            (15981, 16, 5),
            (20997, 24, 6),
            (24576, 32, 8),   # never above 8 (burst VMs)
            (65536, 4, 4),    # never above the VM's vCPUs
            (3072, 8, 2),     # floor of 2
            (65536, 1, 2),
        ):
            r, env = self._lean_threads(mem_mib * 1024, nproc)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(env, f"LEAN_NUM_THREADS={expected}\n", (mem_mib, nproc))
            self.assertIn(f"LEAN_NUM_THREADS={expected}", r.stdout)

    def test_lean_threads_fail_closed_without_memtotal(self) -> None:
        r, env = self._lean_threads(None, 8)
        self.assertNotEqual(r.returncode, 0)
        self.assertEqual(env, "")

    def test_ephemeral_heavy_build_jobs_bound_lean_threads_by_memory(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        def job_body(job: str) -> str:
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            return match.group("body")

        bound_step = (
            "      - name: Bound Lean threads by VM memory\n"
            "{cond}"
            "        run: scripts/ci_lean_threads.sh\n"
        )
        def routed_cond(router: str, job: str) -> str:
            key = job.replace("-", "_")
            return f"        if: needs.{router}.outputs.{key}_on_lean == 'true'\n"

        for job, cond in (
            ("build", ""),
            ("build-audits", routed_cond("route-build", "build-audits")),
            ("build-compiler-binaries", ""),
            ("compiler-audits", routed_cond("route-compiler", "compiler-audits")),
            ("compiler-regressions", ""),
            ("lean-profile", ""),
            ("importer-differential", ""),
        ):
            body = job_body(job)
            # lean.ci can boot an 8-vCPU VM with ~11 GiB, where one Lean/clang
            # process per vCPU failed with ENOMEM: Lake parallelism follows the
            # VM's memory, set once after checkout and before any Lean step.
            step = bound_step.format(cond=cond)
            self.assertEqual(body.count(step), 1, job)
            self.assertLess(body.index("actions/checkout@"), body.index(step), job)
            self.assertLess(body.index(step), body.index("uses: ./.github/actions/setup-lean"), job)
            # A job-level `LEAN_NUM_THREADS:` would hide the $GITHUB_ENV value,
            # and no later step may set it again (step env or $GITHUB_ENV).
            self.assertNotIn("LEAN_NUM_THREADS:", body, job)
            # build-audits keeps exactly one other write: the build-medium cap.
            self.assertEqual(body.count("LEAN_NUM_THREADS="), 1 if job == "build-audits" else 0, job)
        for job in ("build", "build-compiler-binaries", "compiler-regressions", "lean-profile"):
            self.assertIn("runs-on: lean-", job_body(job), job)

        routers = {
            "route-build": ("build", ["build-audits=1", "import-mutations=24"]),
            "route-compiler": (
                "build-compiler-binaries",
                [
                    "compiler-audits=1",
                    "foundry-gas-calibration=1",
                    "foundry=4/2",
                    "foundry-patched=1",
                    "foundry-multi-seed=7/1",
                ],
            ),
        }
        routed = 0
        for router, (after, groups) in routers.items():
            route = job_body(router)
            # Each router runs right before its groups fan out: it needs only the
            # job they wait on, so it starts when they are about to be created.
            self.assertIn(f"    needs: {after}\n", route, router)
            self.assertIn("runs-on: ubuntu-latest", route, router)
            self.assertIn(
                "    permissions:\n      actions: read\n      contents: read\n", route, router
            )
            self.assertIn("ROUTE_POOLS: ${{ vars.ROUTE_POOLS }}\n", route, router)
            self.assertIn("RUNNER_ROUTE: ${{ inputs.runner_route || 'auto' }}\n", route, router)
            self.assertIn("python3 scripts/ci_route_pools.py", route, router)
            for group in groups:
                job = group.split("=")[0]
                key = job.replace("-", "_")
                self.assertIn(f"--group {group}", route, router)
                self.assertIn(f"{key}_runs_on: ${{{{ steps.route.outputs.{key}_runs_on }}}}\n", route)
                self.assertIn(f"{key}_on_lean: ${{{{ steps.route.outputs.{key}_on_lean }}}}\n", route)
                body = job_body(job)
                runs_on = f"runs-on: ${{{{ fromJSON(needs.{router}.outputs.{key}_runs_on) }}}}"
                self.assertIn(runs_on, body, job)
                self.assertEqual(text.count(runs_on), 1, job)
                self.assertRegex(body, rf"(?m)^    needs: \[changes, {router}(, [a-z-]+)*\]$", job)
                self.assertNotIn("_on_lean", body.replace(f"needs.{router}.outputs.{key}_on_lean", ""), job)
                routed += 1
        # Only the routed jobs may land on build-medium, and only through a router.
        self.assertEqual(text.count("runs-on: ${{ fromJSON(needs.route-"), routed)
        self.assertNotIn("needs.route.", text)
        self.assertNotIn("runs-on: [self-hosted, linux, x64, verity, build, build-medium]", text)
        # The built-in pool list (used when ROUTE_POOLS is unset or invalid):
        # build-medium while its 3 runners have room for a group, then lean-8.
        default = re.search(r"(?m)^  VERIFY_ROUTE_POOLS_DEFAULT: '(.*)'$", text)
        self.assertIsNotNone(default)
        self.assertEqual(
            json.loads(default.group(1)),
            [
                {
                    "name": "build-medium",
                    "labels": ["self-hosted", "linux", "x64", "verity", "build", "build-medium"],
                    "slots": 3,
                },
                {"name": "lean-8", "labels": ["lean-8vcpu-ubuntu-2604"]},
            ],
        )
        self.assertRegex(
            job_body("ci-gate"), r"(?m)^    needs: \[changes, route-build, route-compiler, "
        )

        # build-medium keeps main's per-host limits; lean.ci keeps the VM defaults.
        self.assertIn(
            "      - name: Cap Lean threads on build-medium\n"
            "        if: needs.route-build.outputs.build_audits_on_lean != 'true'\n"
            "        run: echo \"LEAN_NUM_THREADS=4\" >> \"$GITHUB_ENV\"\n",
            job_body("build-audits"),
        )
        self.assertIn(
            "max-parallel: ${{ needs.route-compiler.outputs.foundry_on_lean == 'true' && 4 || 2 }}",
            job_body("foundry"),
        )
        self.assertIn(
            "max-parallel: ${{ needs.route-compiler.outputs.foundry_multi_seed_on_lean == 'true'"
            " && 7 || 1 }}",
            job_body("foundry-multi-seed"),
        )
        for job in ("import-mutations", "foundry-gas-calibration", "foundry-patched"):
            self.assertNotIn("max-parallel:", job_body(job), job)

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
