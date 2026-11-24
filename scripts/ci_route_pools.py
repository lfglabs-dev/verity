#!/usr/bin/env python3
"""Pick a runner pool for each routed Verify job group, at fan-out time.

`verify.yml` runs this in `route-build` (right after `build`) and in
`route-compiler` (right after `build-compiler-binaries`), so the decision uses
the runner load at the moment the routed jobs are about to be created.

Pools come from the ROUTE_POOLS repository variable, else
VERIFY_ROUTE_POOLS_DEFAULT: an ordered, non-empty JSON array of
{"name": str, "labels": [str, ...], "slots": int (optional),
"max_queue": int (optional)}.

A job "is on" a pool when its requested labels include all of the pool's
labels (case-insensitive). For every group, in the order given, the first pool
that has room wins; the last pool takes the rest:

- `slots` (the pool's runner count): room when the group's concurrent job
  count fits in slots - in_progress - queued - jobs already routed there by
  this call. The workflow token cannot list self-hosted runners (that needs
  repository administration access), so the runner count is configuration.
- `max_queue`: room while queued + jobs already routed there is below it.
- A pool with both needs both; a pool with neither always has room.

A group is `name=jobs[/cap]`: `jobs` jobs, of which at most `cap` run at once
on a build-medium pool (the workflow's `max-parallel` there). The runner_route
input forces one pool for every group (`lean` means `lean-8` unless a pool is
named `lean`; an unknown name warns and routes automatically). A GitHub API
error routes every group to the first pool, as before.

Outputs, per group with `-` replaced by `_`: `<group>_runs_on` (JSON label
list) and `<group>_on_lean` (`true` when the labels do not include
`build-medium`).

Groups are routed whether or not their jobs will run (a job's own `if` may
skip it: import-mutations outside nightly/dispatch/`ci:mutations`,
foundry-multi-seed on PRs, the Foundry jobs on draft PRs), so the workflow
lists such groups after the ones that always run: their reservation then
never pushes an earlier group off build-medium, only the summary's routed
count includes them. Matrix jobs held back by `max-parallel` are created as
`queued`, so they count against free slots (erring towards lean-8). Jobs of
runs that are `pending`/`waiting` (e.g. behind a concurrency group) are not
counted. Two runs routing within the same few seconds can both see the same
free slots, as with the previous router.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field

MEDIUM_LABEL = "build-medium"
ACTIVE_STATUSES = ("queued", "in_progress")


@dataclass
class Group:
    name: str
    jobs: int
    medium_cap: int | None = None

    def demand(self, pool: dict) -> int:
        if self.medium_cap is not None and not on_lean(pool):
            return min(self.jobs, self.medium_cap)
        return self.jobs

    @property
    def key(self) -> str:
        return self.name.replace("-", "_")


@dataclass
class Decision:
    group: Group
    pool: int
    reason: str


@dataclass
class Load:
    queued: int = 0
    in_progress: int = 0
    routed: int = 0
    routed_groups: list[str] = field(default_factory=list)


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def valid_pools(pools: object) -> bool:
    if not isinstance(pools, list) or not pools:
        return False
    for pool in pools:
        if not isinstance(pool, dict):
            return False
        name, labels = pool.get("name"), pool.get("labels")
        if not isinstance(name, str) or not name:
            return False
        if not isinstance(labels, list) or not labels:
            return False
        if not all(isinstance(label, str) and label for label in labels):
            return False
        for key in ("slots", "max_queue"):
            if key in pool and not _is_int(pool[key]):
                return False
    return True


def load_pools(override: str, default: str) -> tuple[list[dict], str, list[str]]:
    """Return (pools, source, warnings). An invalid built-in default raises."""
    warnings: list[str] = []
    if override.strip():
        try:
            pools = json.loads(override)
        except json.JSONDecodeError:
            pools = None
        if valid_pools(pools):
            return pools, "ROUTE_POOLS repository variable", warnings
        warnings.append("ROUTE_POOLS is not a valid pool list; using the built-in default")
    pools = json.loads(default)
    if not valid_pools(pools):
        raise ValueError("VERIFY_ROUTE_POOLS_DEFAULT is not a valid pool list")
    return pools, "built-in default", warnings


def parse_group(spec: str) -> Group:
    name, sep, count = spec.partition("=")
    if not sep or not name:
        raise ValueError(f"group {spec!r} is not name=jobs[/cap]")
    jobs, _, cap = count.partition("/")
    group = Group(name, int(jobs), int(cap) if cap else None)
    if group.jobs < 1 or (group.medium_cap is not None and group.medium_cap < 1):
        raise ValueError(f"group {spec!r} needs positive counts")
    return group


def on_lean(pool: dict) -> bool:
    return MEDIUM_LABEL not in pool["labels"]


def _lower(labels: list[str]) -> set[str]:
    return {label.lower() for label in labels}


def pool_loads(pools: list[dict], jobs: list[dict]) -> list[Load]:
    loads = [Load() for _ in pools]
    for job in jobs:
        status = job.get("status")
        if status not in ACTIVE_STATUSES:
            continue
        have = _lower(job.get("labels") or [])
        for pool, load in zip(pools, loads):
            if _lower(pool["labels"]) <= have:
                if status == "queued":
                    load.queued += 1
                else:
                    load.in_progress += 1
    return loads


def _room(pool: dict, load: Load, demand: int) -> tuple[bool, str]:
    parts, ok = [], True
    if "slots" in pool:
        free = pool["slots"] - load.in_progress - load.queued - load.routed
        ok = ok and demand <= free
        parts.append(
            f"{demand} job(s) vs {max(free, 0)} free of {pool['slots']} slots "
            f"({load.in_progress} running, {load.queued} queued, {load.routed} routed by this job)"
        )
    if "max_queue" in pool:
        depth = load.queued + load.routed
        ok = ok and depth < pool["max_queue"]
        parts.append(f"queue {depth} vs max_queue {pool['max_queue']}")
    if not parts:
        parts.append("no slots or max_queue limit")
    return ok, "; ".join(parts)


def resolve_forced(pools: list[dict], route: str) -> tuple[int | None, list[str]]:
    route = (route or "auto").strip()
    if route == "lean" and not any(p["name"] == "lean" for p in pools):
        route = "lean-8"
    if route in ("", "auto"):
        return None, []
    for i, pool in enumerate(pools):
        if pool["name"] == route:
            return i, []
    return None, [f"unknown pool '{route}' in runner_route; routing automatically"]


def choose(
    pools: list[dict], groups: list[Group], jobs: list[dict] | None, forced: int | None
) -> tuple[list[Decision], list[Load] | None]:
    if forced is not None:
        return [Decision(g, forced, "forced by the runner_route input") for g in groups], None
    if jobs is None:
        reason = "GitHub API error; falling back to the first pool"
        return [Decision(g, 0, reason) for g in groups], None
    loads = pool_loads(pools, jobs)
    decisions = []
    last = len(pools) - 1
    for group in groups:
        notes = []
        for i, pool in enumerate(pools):
            demand = group.demand(pool)
            ok, detail = _room(pool, loads[i], demand)
            if i == last and not ok:
                ok = True
                detail = "every earlier pool is full; last pool takes the rest"
                if notes:
                    detail += " (" + "; ".join(notes) + ")"
            elif not ok:
                notes.append(f"{pool['name']} full: {detail}")
                continue
            elif notes:
                detail += " (" + "; ".join(notes) + ")"
            loads[i].routed += demand
            loads[i].routed_groups.append(group.name)
            decisions.append(Decision(group, i, f"{pool['name']}: {detail}"))
            break
    return decisions, loads


def fetch_jobs(repo: str) -> list[dict] | None:
    """Queued and in-progress jobs of every queued or in-progress run, or None."""

    def gh(path: str, jq: str) -> list[str]:
        out = subprocess.run(
            ["gh", "api", "--paginate", path, "--jq", jq],
            check=True,
            capture_output=True,
            text=True,
        ).stdout
        return [line for line in out.splitlines() if line.strip()]

    try:
        run_ids: set[str] = set()
        for status in ACTIVE_STATUSES:
            run_ids.update(
                gh(f"repos/{repo}/actions/runs?status={status}&per_page=100", ".workflow_runs[].id")
            )
        jobs = []
        for run_id in sorted(run_ids):
            for line in gh(
                f"repos/{repo}/actions/runs/{run_id}/jobs?filter=latest&per_page=100",
                '.jobs[] | select(.status == "queued" or .status == "in_progress")'
                " | {status, labels} | tojson",
            ):
                jobs.append(json.loads(line))
        return jobs
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError):
        return None


def render(
    decisions: list[Decision],
    pools: list[dict],
    loads: list[Load] | None,
    source: str,
    mode: str,
    title: str,
) -> tuple[list[str], list[str]]:
    outputs, summary = [], [f"### Runner route: {title}", ""]
    for d in decisions:
        pool = pools[d.pool]
        runs_on = json.dumps(pool["labels"], separators=(",", ":"))
        outputs.append(f"{d.group.key}_runs_on={runs_on}")
        outputs.append(f"{d.group.key}_on_lean={'true' if on_lean(pool) else 'false'}")
        summary.append(
            f"- `{d.group.name}` ({d.group.jobs} job(s)) -> `{pool['name']}` "
            f"(`runs-on: {runs_on}`): {d.reason}"
        )
    summary += ["", f"Mode `{mode}`; pools from the {source}, in order:"]
    for i, pool in enumerate(pools):
        limits = ", ".join(f"{k} {pool[k]}" for k in ("slots", "max_queue") if k in pool) or "rest"
        if loads is None:
            usage = "load n/a"
        else:
            load = loads[i]
            usage = f"{load.in_progress} running, {load.queued} queued, {load.routed} routed here"
        summary.append(f"- `{pool['name']}` {json.dumps(pool['labels'])}: {limits}; {usage}")
    return outputs, summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--title", required=True, help="Summary heading, e.g. the fan-out point")
    parser.add_argument("--group", action="append", required=True, type=parse_group)
    args = parser.parse_args(argv)

    mode = os.environ.get("RUNNER_ROUTE", "") or "auto"
    pools, source, warnings = load_pools(
        os.environ.get("ROUTE_POOLS", ""), os.environ["VERIFY_ROUTE_POOLS_DEFAULT"]
    )
    forced, forced_warnings = resolve_forced(pools, mode)
    warnings += forced_warnings
    jobs = None if forced is not None else fetch_jobs(os.environ["REPO"])
    if forced is None and jobs is None:
        warnings.append("GitHub API error; falling back to the first pool")
    decisions, loads = choose(pools, args.group, jobs, forced)
    outputs, summary = render(decisions, pools, loads, source, mode, args.title)

    for warning in warnings:
        print(f"::warning::runner route: {warning}")
    for d in decisions:
        print(f"runner route: {d.group.name} -> {pools[d.pool]['name']} ({d.reason})")
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as fh:
        fh.write("\n".join(outputs) + "\n")
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with open(summary_path, "a", encoding="utf-8") as fh:
            fh.write("\n".join(summary) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
