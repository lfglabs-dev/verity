#!/usr/bin/env python3
"""Tests for scripts/ci_route_pools.py (Verify's fan-out runner routing)."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import ci_route_pools as rp  # noqa: E402

VERIFY_WORKFLOW = SCRIPTS.parent / ".github" / "workflows" / "verify.yml"
MEDIUM = ["self-hosted", "linux", "x64", "verity", "build", "build-medium"]
LEAN8 = ["lean-8vcpu-ubuntu-2604"]
LEAN4 = ["lean-4vcpu-ubuntu-2604"]


def default_pools_text() -> str:
    text = VERIFY_WORKFLOW.read_text(encoding="utf-8")
    match = re.search(r"(?m)^  VERIFY_ROUTE_POOLS_DEFAULT: '(.*)'$", text)
    assert match is not None
    return match.group(1)


def jobs(medium_running: int = 0, medium_queued: int = 0, lean_queued: int = 0) -> list[dict]:
    return (
        [{"status": "in_progress", "labels": MEDIUM}] * medium_running
        + [{"status": "queued", "labels": MEDIUM}] * medium_queued
        + [{"status": "queued", "labels": LEAN8}] * lean_queued
    )


AFTER_BUILD = [rp.parse_group("build-audits=1"), rp.parse_group("import-mutations=24")]
AFTER_COMPILER = [
    rp.parse_group(g)
    for g in (
        "compiler-audits=1",
        "foundry-gas-calibration=1",
        "foundry=4/2",
        "foundry-patched=1",
        "foundry-multi-seed=7/1",
    )
]


class RoutePoolsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.pools, self.source, warnings = rp.load_pools("", default_pools_text())
        self.assertEqual(warnings, [])
        self.assertEqual(self.source, "built-in default")

    def names(self, pools, groups, job_list, forced=None) -> dict[str, str]:
        decisions, _ = rp.choose(pools, groups, job_list, forced)
        self.assertEqual([d.group.name for d in decisions], [g.name for g in groups])
        return {d.group.name: pools[d.pool]["name"] for d in decisions}

    def test_default_prefers_build_medium_when_idle(self) -> None:
        self.assertEqual(
            self.names(self.pools, AFTER_COMPILER[:2], jobs()),
            {"compiler-audits": "build-medium", "foundry-gas-calibration": "build-medium"},
        )

    def test_busy_runners_spill_to_lean(self) -> None:
        # All 3 build-medium runners busy, nothing queued: nothing fits.
        routed = self.names(self.pools, AFTER_COMPILER, jobs(medium_running=3))
        self.assertEqual(set(routed.values()), {"lean-8"})
        # One busy: 2 free slots for the first groups that fit.
        routed = self.names(self.pools, AFTER_COMPILER, jobs(medium_running=1))
        self.assertEqual(
            routed,
            {
                "compiler-audits": "build-medium",
                "foundry-gas-calibration": "build-medium",
                "foundry": "lean-8",
                "foundry-patched": "lean-8",
                "foundry-multi-seed": "lean-8",
            },
        )

    def test_queued_jobs_take_free_slots(self) -> None:
        routed = self.names(self.pools, AFTER_COMPILER[:1], jobs(medium_running=1, medium_queued=2))
        self.assertEqual(routed, {"compiler-audits": "lean-8"})
        # Jobs queued on another pool do not count against build-medium.
        routed = self.names(self.pools, AFTER_COMPILER[:1], jobs(lean_queued=40))
        self.assertEqual(routed, {"compiler-audits": "build-medium"})

    def test_fan_out_larger_than_free_capacity(self) -> None:
        # A 24-shard matrix never fits 3 runners; build-audits still does.
        self.assertEqual(
            self.names(self.pools, AFTER_BUILD, jobs()),
            {"build-audits": "build-medium", "import-mutations": "lean-8"},
        )
        # Idle pool, whole compiler wave: first fit in group order, using the
        # build-medium max-parallel for the throttled matrices (foundry 2).
        self.assertEqual(
            self.names(self.pools, AFTER_COMPILER, jobs()),
            {
                "compiler-audits": "build-medium",
                "foundry-gas-calibration": "build-medium",
                "foundry": "lean-8",
                "foundry-patched": "build-medium",
                "foundry-multi-seed": "lean-8",
            },
        )

    def test_matrix_cap_applies_only_on_build_medium(self) -> None:
        group = rp.parse_group("foundry=4/2")
        self.assertEqual(group.demand(self.pools[0]), 2)
        self.assertEqual(group.demand(self.pools[1]), 4)
        routed = self.names(self.pools, [group], jobs(medium_running=1))
        self.assertEqual(routed, {"foundry": "build-medium"})

    def test_run_45485073018_timeline(self) -> None:
        # 21:48Z: build-compiler-binaries done; build-audits (this run) held
        # old-agent and another run's jobs held ashur and nippur, with more
        # queued. The old route (decided at 20:51Z, before those jobs existed)
        # pinned all 16 jobs to build-medium; now every compiler group goes to
        # lean-8, which was idle.
        routed = self.names(self.pools, AFTER_COMPILER, jobs(medium_running=3, medium_queued=1))
        self.assertEqual(set(routed.values()), {"lean-8"})
        _, loads = rp.choose(self.pools, AFTER_COMPILER, jobs(medium_running=3, medium_queued=1), None)
        self.assertEqual((loads[0].in_progress, loads[0].queued, loads[0].routed), (3, 1, 0))

    def test_api_error_falls_back_to_first_pool(self) -> None:
        decisions, loads = rp.choose(self.pools, AFTER_COMPILER, None, None)
        self.assertIsNone(loads)
        self.assertEqual({d.pool for d in decisions}, {0})
        self.assertIn("GitHub API error", decisions[0].reason)

    def test_forced_runner_route(self) -> None:
        for mode, expected in (("lean", "lean-8"), ("lean-8", "lean-8"), ("build-medium", "build-medium")):
            forced, warnings = rp.resolve_forced(self.pools, mode)
            self.assertEqual(warnings, [])
            routed = self.names(self.pools, AFTER_COMPILER, jobs(medium_queued=50), forced)
            self.assertEqual(set(routed.values()), {expected}, mode)
        for mode in ("auto", ""):
            self.assertEqual(rp.resolve_forced(self.pools, mode), (None, []))
        forced, warnings = rp.resolve_forced(self.pools, "nope")
        self.assertIsNone(forced)
        self.assertIn("unknown pool 'nope'", warnings[0])

    def test_max_queue_pools_keep_their_semantics(self) -> None:
        three = json.dumps(
            [
                {"name": "build-medium", "labels": MEDIUM, "max_queue": 2},
                {"name": "lean-4", "labels": LEAN4, "max_queue": 1},
                {"name": "lean-8", "labels": LEAN8},
            ]
        )
        pools, source, warnings = rp.load_pools(three, default_pools_text())
        self.assertEqual((source, warnings), ("ROUTE_POOLS repository variable", []))
        one = AFTER_COMPILER[:1]
        # Below max_queue wins; running jobs do not count against max_queue.
        self.assertEqual(self.names(pools, one, jobs(medium_running=9, medium_queued=1)),
                         {"compiler-audits": "build-medium"})
        self.assertEqual(self.names(pools, one, jobs(medium_queued=2)), {"compiler-audits": "lean-4"})
        lean4_queued = [{"status": "queued", "labels": LEAN4}]
        self.assertEqual(self.names(pools, one, jobs(medium_queued=2) + lean4_queued),
                         {"compiler-audits": "lean-8"})
        # A pool counts jobs carrying all of its labels, case-insensitively.
        self.assertEqual(
            self.names(pools, one, [{"status": "queued", "labels": ["build-medium"]}] * 9),
            {"compiler-audits": "build-medium"},
        )
        upper = [{"status": "queued", "labels": [label.upper() for label in MEDIUM]}] * 2
        self.assertEqual(self.names(pools, one, upper), {"compiler-audits": "lean-4"})
        # Groups routed earlier in the same call count as queued.
        two = [rp.parse_group("a=1"), rp.parse_group("b=1"), rp.parse_group("c=1")]
        self.assertEqual(self.names(pools, two, jobs()), {"a": "build-medium", "b": "build-medium", "c": "lean-4"})

    def test_invalid_route_pools_fall_back_to_default(self) -> None:
        for bad in (
            '[{"name":"x"',
            "[]",
            "{}",
            '[{"name":"x","labels":[]}]',
            '[{"name":"","labels":["a"]}]',
            '[{"name":"x","labels":["a"],"max_queue":"6"}]',
            '[{"name":"x","labels":["a"],"slots":-1}]',
            '[{"name":"x","labels":["a"],"slots":true}]',
            '[{"name":"x","labels":["a"],"slots":1.5}]',
        ):
            pools, source, warnings = rp.load_pools(bad, default_pools_text())
            self.assertEqual(pools, self.pools, bad)
            self.assertEqual(source, "built-in default", bad)
            self.assertIn("ROUTE_POOLS is not a valid pool list", warnings[0], bad)
        with self.assertRaises(ValueError):
            rp.load_pools("", "[]")

    def test_parse_group_rejects_bad_specs(self) -> None:
        for bad in ("foundry", "=1", "foundry=0", "foundry=4/0", "foundry=x"):
            with self.assertRaises(ValueError, msg=bad):
                rp.parse_group(bad)


class RoutePoolsCliTest(unittest.TestCase):
    """End to end: the CLI against a fake `gh`, as the router jobs run it."""

    def run_cli(self, mode: str, job_list: list[dict] | None, pools: str = "") -> tuple[dict, str, str]:
        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            fake = tmp_path / "gh"
            (tmp_path / "jobs").write_text(
                "".join(json.dumps(j) + "\n" for j in (job_list or [])), encoding="utf-8"
            )
            fake.write_text(
                "#!/usr/bin/env bash\n"
                f'echo "$*" >> "{tmp_path}/calls"\n'
                '[ "${FAKE_FAIL:-0}" = 1 ] && exit 1\n'
                'case "$*" in\n'
                f'  *"/runs/11/jobs"*) cat "{tmp_path}/jobs" ;;\n'
                '  *"/jobs"*) ;;\n'
                "  *status=queued*) echo 11 ;;\n"
                "  *status=in_progress*) printf '11\\n12\\n' ;;\n"
                "esac\n",
                encoding="utf-8",
            )
            fake.chmod(0o755)
            out, summary = tmp_path / "out", tmp_path / "summary"
            proc = subprocess.run(
                [
                    sys.executable,
                    str(SCRIPTS / "ci_route_pools.py"),
                    "--title",
                    "after build-compiler-binaries",
                    *[arg for g in ("compiler-audits=1", "foundry=4/2") for arg in ("--group", g)],
                ],
                check=True,
                capture_output=True,
                text=True,
                env=dict(
                    os.environ,
                    PATH=f"{tmp}:{os.environ['PATH']}",
                    GITHUB_OUTPUT=str(out),
                    GITHUB_STEP_SUMMARY=str(summary),
                    REPO="o/r",
                    RUNNER_ROUTE=mode,
                    ROUTE_POOLS=pools,
                    VERIFY_ROUTE_POOLS_DEFAULT=default_pools_text(),
                    FAKE_FAIL="1" if job_list is None else "0",
                ),
            )
            outputs = dict(line.split("=", 1) for line in out.read_text().splitlines())
            calls = (tmp_path / "calls").read_text() if (tmp_path / "calls").exists() else ""
            return outputs, proc.stdout + summary.read_text(), calls

    def test_outputs_and_summary(self) -> None:
        outputs, text, calls = self.run_cli("auto", jobs(medium_running=1, medium_queued=1))
        self.assertEqual(
            outputs,
            {
                "compiler_audits_runs_on": json.dumps(MEDIUM, separators=(",", ":")),
                "compiler_audits_on_lean": "false",
                "foundry_runs_on": json.dumps(LEAN8, separators=(",", ":")),
                "foundry_on_lean": "true",
            },
        )
        # Each run's jobs are read once, even when listed by both statuses.
        self.assertEqual(calls.count("/actions/runs/11/jobs"), 1)
        self.assertEqual(calls.count("/actions/runs/12/jobs"), 1)
        self.assertIn("### Runner route: after build-compiler-binaries", text)
        self.assertIn("`foundry` (4 job(s)) -> `lean-8`", text)
        self.assertIn("build-medium full: 2 job(s) vs 0 free of 3 slots", text)
        self.assertIn("1 running, 1 queued, 1 routed here", text)
        self.assertNotIn("::warning::", text)

    def test_api_error_and_forced_and_invalid(self) -> None:
        outputs, text, _ = self.run_cli("auto", None)
        self.assertEqual(outputs["foundry_on_lean"], "false")
        self.assertIn("::warning::runner route: GitHub API error; falling back to the first pool", text)
        outputs, text, calls = self.run_cli("lean", jobs())
        self.assertEqual(outputs["compiler_audits_on_lean"], "true")
        self.assertEqual(calls, "")  # a forced route never calls the API
        outputs, text, _ = self.run_cli("auto", jobs(medium_running=3), pools='[{"name":"x"}]')
        self.assertEqual(outputs["compiler_audits_on_lean"], "true")
        self.assertIn("ROUTE_POOLS is not a valid pool list", text)


if __name__ == "__main__":
    unittest.main()
