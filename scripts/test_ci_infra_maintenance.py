#!/usr/bin/env python3
from __future__ import annotations

import fcntl
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
        # Fastlane jobs are script-only. Pinning an arch or a single host made
        # the DGX arbiter's lowest-priority runner the only eligible executor,
        # wedging every workflow behind changes/checks during P0 campaigns;
        # redundant runners (e.g. the cgroup-capped x64 one on agent-core)
        # must also qualify.
        self.assertNotIn(
            "runs-on: [self-hosted, linux, ARM64, dgx-spark, verity, fastlane]", text
        )
        for job in ("changes", "checks", "timeout-watchdog", "failure-hints"):
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            self.assertIn(
                "runs-on: [self-hosted, linux, verity, fastlane]",
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
            payload = work_a / "lean-workspace-build.tar"
            subprocess.run(["tar", "-cf", str(payload), "-C", str(ROOT), "README.md"], check=True)
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

    def test_parallel_build_jobs_use_four_lean_threads(self) -> None:
        text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
        for job in (
            "build-compiler-binaries",
            "compiler-regressions",
        ):
            match = re.search(rf"^  {job}:\n(?P<body>.*?)(?=^  [a-zA-Z0-9_-]+:|\Z)", text, re.S | re.M)
            self.assertIsNotNone(match, job)
            body = match.group("body")
            self.assertIn("LEAN_NUM_THREADS: 4", body, job)
            self.assertNotIn("LEAN_NUM_THREADS: 8", body, job)


if __name__ == "__main__":
    unittest.main()
