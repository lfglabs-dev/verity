#!/usr/bin/env python3
from __future__ import annotations

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
