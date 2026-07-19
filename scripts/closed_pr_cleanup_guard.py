#!/usr/bin/env python3
"""Fail-closed guard for closed-PR cleanup under GitHub native Stacked PRs.

Decides whether closed-pr-cleanup may perform destructive work (cancel runs,
delete the head branch, remove PR-scoped artifacts, close dependents, etc.).

Eligibility is fail-closed:
  - cleanup is allowed only when stack membership and open dependents can be
    ruled out with clear evidence
  - Stacks REST API failures, empty/malformed payloads, or ambiguous metadata
    retain the branch/PR/artifacts
  - a direct open-PR base-ref check always runs as a beta/API-lag fallback

This module performs no cleanup itself. Callers must honor the decision.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

DEFAULT_API_VERSION = "2022-11-28"
DEFAULT_ACCEPT = "application/vnd.github+json"

# Injectable HTTP getter: (url, headers) -> (status_code, body_text)
HttpGetter = Callable[[str, Mapping[str, str]], tuple[int, str]]


@dataclass(frozen=True)
class GuardDecision:
    """Outcome of the closed-PR cleanup guard."""

    eligible_for_cleanup: bool
    reason: str
    retain_reasons: tuple[str, ...] = ()

    def to_public_dict(self) -> dict[str, Any]:
        return {
            "eligible_for_cleanup": self.eligible_for_cleanup,
            "reason": self.reason,
            "retain_reasons": list(self.retain_reasons),
        }


class GuardError(Exception):
    """Internal guard evaluation error (always treated as retain)."""


def _normalize_repo(repo: str) -> tuple[str, str]:
    parts = repo.strip().split("/")
    if len(parts) != 2 or not parts[0] or not parts[1]:
        raise GuardError(f"invalid repository slug: {repo!r}")
    return parts[0], parts[1]


def parse_stack_metadata(raw: Any) -> tuple[dict[str, Any] | None, str | None]:
    """Parse pull-request ``.stack`` metadata.

    Returns (stack_dict_or_none, error_reason_or_none).
    ``None`` raw means "field absent/null" (not an error).
    Empty objects, wrong types, or missing required fields are malformed.
    """
    if raw is None:
        return None, None
    if raw == "":
        return None, "stack metadata is empty string"
    if isinstance(raw, str):
        text = raw.strip()
        if not text or text in ("null", "undefined"):
            return None, None
        try:
            raw = json.loads(text)
        except json.JSONDecodeError as exc:
            return None, f"stack metadata is not valid JSON: {exc}"
    if raw is None:
        return None, None
    if not isinstance(raw, dict):
        return None, f"stack metadata must be an object, got {type(raw).__name__}"
    if not raw:
        return None, "stack metadata object is empty"
    if "__malformed__" in raw:
        return None, str(raw["__malformed__"])
    # Official fields: id, number, size, position, base
    required_any = ("id", "number")
    if not any(key in raw for key in required_any):
        return None, "stack metadata missing id/number"
    for key in ("size", "position"):
        if key in raw and raw[key] is not None and not isinstance(raw[key], int):
            return None, f"stack metadata field {key!r} must be int or null"
    return raw, None


def stack_metadata_implies_retain(stack: dict[str, Any]) -> str | None:
    """If PR stack metadata indicates active stack membership, return reason."""
    size = stack.get("size")
    position = stack.get("position")
    # Any well-formed stack object on a PR means it is a stack member.
    # Retain whenever the stack still has (or had) multiple members, or when
    # size is unknown/ambiguous.
    if size is None:
        return "PR stack metadata present without size (ambiguous membership)"
    if not isinstance(size, int) or size < 1:
        return f"PR stack metadata has invalid size={size!r}"
    if size >= 2:
        pos_note = f", position={position}" if isinstance(position, int) else ""
        return f"PR is a native stack member (stack size={size}{pos_note})"
    # size == 1: single-PR "stack" — still treat as stack-tagged; retain only
    # if position claims a multi-stack layout (defensive).
    if isinstance(position, int) and position > 1:
        return f"PR stack position={position} inconsistent with size=1"
    return None


def parse_stacks_list_payload(raw: Any) -> tuple[list[dict[str, Any]] | None, str | None]:
    """Parse GET /repos/{owner}/{repo}/stacks response body."""
    if raw is None:
        return None, "stacks API payload is null"
    if isinstance(raw, str):
        text = raw.strip()
        if not text:
            return None, "stacks API payload is empty"
        try:
            raw = json.loads(text)
        except json.JSONDecodeError as exc:
            return None, f"stacks API payload is not valid JSON: {exc}"
    # Some gateways wrap list payloads.
    if isinstance(raw, dict):
        if "stacks" in raw and isinstance(raw["stacks"], list):
            raw = raw["stacks"]
        elif "data" in raw and isinstance(raw["data"], list):
            raw = raw["data"]
        else:
            return None, "stacks API payload object missing stacks list"
    if not isinstance(raw, list):
        return None, f"stacks API payload must be a list, got {type(raw).__name__}"
    stacks: list[dict[str, Any]] = []
    for index, item in enumerate(raw):
        if not isinstance(item, dict):
            return None, f"stacks API item[{index}] is not an object"
        stacks.append(item)
    return stacks, None


def stack_resource_involves_pr_or_branch(
    stack: dict[str, Any],
    *,
    pr_number: int,
    head_branch: str,
) -> tuple[bool, str | None]:
    """Return (involved, ambiguity_reason)."""
    pull_requests = stack.get("pull_requests")
    if pull_requests is None:
        # Without members we cannot clear the stack; treat as ambiguous if open.
        open_flag = stack.get("open")
        if open_flag is True:
            return True, "open stack resource missing pull_requests list"
        if open_flag is False:
            return False, None
        return True, "stack resource missing pull_requests and open flag"
    if not isinstance(pull_requests, list):
        return True, "stack pull_requests is not a list"

    branch = head_branch.strip()
    saw_member = False
    saw_open_other = False
    for entry in pull_requests:
        if not isinstance(entry, dict):
            return True, "stack pull_requests contains non-object entry"
        number = entry.get("number")
        state = str(entry.get("state") or "").lower()
        head = entry.get("head")
        head_ref = None
        if isinstance(head, dict):
            ref = head.get("ref")
            if isinstance(ref, str):
                head_ref = ref
        elif isinstance(entry.get("head_ref"), str):
            head_ref = entry["head_ref"]

        is_self = number == pr_number or (head_ref is not None and head_ref == branch)
        if is_self:
            saw_member = True
        elif state in {"open", "draft"} or entry.get("merged_at") in (None, "") and state != "closed":
            # Count non-closed peers as dependents still needing the stack.
            if state != "closed" and entry.get("merged_at") is None:
                saw_open_other = True

    open_flag = stack.get("open")
    if saw_member and (saw_open_other or open_flag is True):
        stack_no = stack.get("number", stack.get("id", "?"))
        return True, f"PR/branch is member of open native stack {stack_no}"
    if saw_member and open_flag is None and saw_open_other is False:
        # Member of a stack with no clear open peers — still retain: the closed
        # PR's branch may remain the base until GitHub retargets dependents.
        stack_no = stack.get("number", stack.get("id", "?"))
        return True, f"PR/branch is member of native stack {stack_no} (open state unclear)"
    if open_flag is True and not pull_requests:
        return True, "open stack has empty pull_requests"
    return False, None


def parse_pulls_list_payload(raw: Any) -> tuple[list[dict[str, Any]] | None, str | None]:
    if raw is None:
        return None, "pulls payload is null"
    if isinstance(raw, str):
        text = raw.strip()
        if not text:
            return None, "pulls payload is empty"
        try:
            raw = json.loads(text)
        except json.JSONDecodeError as exc:
            return None, f"pulls payload is not valid JSON: {exc}"
    if not isinstance(raw, list):
        return None, f"pulls payload must be a list, got {type(raw).__name__}"
    pulls: list[dict[str, Any]] = []
    for index, item in enumerate(raw):
        if not isinstance(item, dict):
            return None, f"pulls item[{index}] is not an object"
        pulls.append(item)
    return pulls, None


def open_dependents_on_branch(
    pulls: list[dict[str, Any]],
    *,
    head_branch: str,
    closed_pr_number: int,
) -> list[int]:
    """Return open PR numbers whose base ref is ``head_branch``."""
    branch = head_branch.strip()
    dependents: list[int] = []
    for pr in pulls:
        number = pr.get("number")
        if number == closed_pr_number:
            continue
        state = str(pr.get("state") or "").lower()
        if state != "open":
            continue
        base = pr.get("base")
        base_ref = None
        if isinstance(base, dict):
            ref = base.get("ref")
            if isinstance(ref, str):
                base_ref = ref
        elif isinstance(pr.get("base_ref"), str):
            base_ref = pr["base_ref"]
        if base_ref == branch and isinstance(number, int):
            dependents.append(number)
    return dependents


def default_http_getter(token: str | None = None) -> HttpGetter:
    def _get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
        req_headers = dict(headers)
        auth = token if token is not None else os.environ.get("GH_TOKEN") or os.environ.get(
            "GITHUB_TOKEN"
        )
        if auth:
            req_headers.setdefault("Authorization", f"Bearer {auth}")
        request = urllib.request.Request(url, headers=req_headers, method="GET")
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                body = response.read().decode("utf-8")
                return int(response.status), body
        except urllib.error.HTTPError as exc:
            body = exc.read().decode("utf-8", errors="replace")
            return int(exc.code), body
        except urllib.error.URLError as exc:
            raise GuardError(f"HTTP transport error for {url}: {exc}") from exc

    return _get


def _api_headers(api_version: str = DEFAULT_API_VERSION) -> dict[str, str]:
    return {
        "Accept": DEFAULT_ACCEPT,
        "X-GitHub-Api-Version": api_version,
        "User-Agent": "verity-closed-pr-cleanup-guard",
    }


def fetch_stacks(
    *,
    repo: str,
    pull_request: int | None,
    http_get: HttpGetter,
    api_version: str = DEFAULT_API_VERSION,
) -> tuple[list[dict[str, Any]] | None, str | None]:
    """GET /repos/{owner}/{repo}/stacks, optionally filtered by pull_request."""
    owner, name = _normalize_repo(repo)
    query = ""
    if pull_request is not None:
        query = "?" + urllib.parse.urlencode({"pull_request": str(pull_request)})
    url = f"https://api.github.com/repos/{owner}/{name}/stacks{query}"
    try:
        status, body = http_get(url, _api_headers(api_version))
    except GuardError as exc:
        return None, str(exc)
    # 404: stacks private preview not enabled for this repo, or no such route.
    # That is a clear "no native stacks" signal — preserve standalone cleanup.
    # Transport failures, 5xx, and malformed 200 bodies remain fail-closed.
    if status == 404:
        return [], None
    if status == 204:
        return [], None
    if status in {401, 403}:
        # Auth/permission ambiguity: cannot rule out stack membership.
        return None, f"stacks API returned HTTP {status} (ambiguous authorization)"
    if status != 200:
        return None, f"stacks API returned HTTP {status}"
    return parse_stacks_list_payload(body)


def fetch_open_pulls(
    *,
    repo: str,
    http_get: HttpGetter,
    api_version: str = DEFAULT_API_VERSION,
    per_page: int = 100,
) -> tuple[list[dict[str, Any]] | None, str | None]:
    owner, name = _normalize_repo(repo)
    pulls: list[dict[str, Any]] = []
    page = 1
    while True:
        query = urllib.parse.urlencode(
            {"state": "open", "per_page": str(per_page), "page": str(page)}
        )
        url = f"https://api.github.com/repos/{owner}/{name}/pulls?{query}"
        try:
            status, body = http_get(url, _api_headers(api_version))
        except GuardError as exc:
            return None, str(exc)
        if status != 200:
            return None, f"pulls API returned HTTP {status}"
        page_items, err = parse_pulls_list_payload(body)
        if err:
            return None, err
        assert page_items is not None
        pulls.extend(page_items)
        if len(page_items) < per_page:
            break
        page += 1
        if page > 50:
            return None, "pulls API pagination exceeded safety cap"
    return pulls, None


def evaluate_guard(
    *,
    repo: str,
    pr_number: int,
    head_branch: str,
    stack_metadata: Any = None,
    stacks: list[dict[str, Any]] | None = None,
    stacks_error: str | None = None,
    open_pulls: list[dict[str, Any]] | None = None,
    open_pulls_error: str | None = None,
) -> GuardDecision:
    """Pure decision function over already-fetched inputs (test seam)."""
    if not isinstance(pr_number, int) or pr_number <= 0:
        return GuardDecision(
            False,
            "malformed closed PR number",
            ("malformed closed PR number",),
        )
    if not isinstance(head_branch, str) or not head_branch.strip():
        return GuardDecision(
            False,
            "malformed head branch",
            ("malformed head branch",),
        )
    try:
        _normalize_repo(repo)
    except GuardError as exc:
        return GuardDecision(False, str(exc), (str(exc),))

    retain: list[str] = []

    stack_obj, stack_err = parse_stack_metadata(stack_metadata)
    if stack_err:
        retain.append(stack_err)
    elif stack_obj is not None:
        meta_reason = stack_metadata_implies_retain(stack_obj)
        if meta_reason:
            retain.append(meta_reason)

    if stacks_error:
        retain.append(f"stacks API unavailable/ambiguous: {stacks_error}")
    elif stacks is None:
        retain.append("stacks API result missing (ambiguous)")
    else:
        for stack in stacks:
            involved, reason = stack_resource_involves_pr_or_branch(
                stack, pr_number=pr_number, head_branch=head_branch
            )
            if involved and reason:
                retain.append(reason)
            elif involved:
                retain.append("PR/branch involved in native stack")

    if open_pulls_error:
        retain.append(f"dependent PR check unavailable: {open_pulls_error}")
    elif open_pulls is None:
        retain.append("dependent PR list missing (ambiguous)")
    else:
        deps = open_dependents_on_branch(
            open_pulls, head_branch=head_branch, closed_pr_number=pr_number
        )
        if deps:
            shown = ", ".join(f"#{n}" for n in deps[:10])
            extra = "" if len(deps) <= 10 else f" (+{len(deps) - 10} more)"
            retain.append(
                f"branch {head_branch!r} is base of open dependent PR(s): {shown}{extra}"
            )

    if retain:
        return GuardDecision(
            eligible_for_cleanup=False,
            reason="retain: " + "; ".join(retain),
            retain_reasons=tuple(retain),
        )
    return GuardDecision(
        eligible_for_cleanup=True,
        reason="eligible: not a native stack member and no open dependent PRs",
        retain_reasons=(),
    )


def run_guard(
    *,
    repo: str,
    pr_number: int,
    head_branch: str,
    stack_metadata: Any = None,
    http_get: HttpGetter | None = None,
    api_version: str = DEFAULT_API_VERSION,
) -> GuardDecision:
    """Fetch Stacks + open pulls (via http_get) and evaluate."""
    getter = http_get or default_http_getter()
    stacks, stacks_error = fetch_stacks(
        repo=repo,
        pull_request=pr_number,
        http_get=getter,
        api_version=api_version,
    )
    # If filter endpoint is odd, also try unfiltered list when first call failed
    # with a parse error on non-list — already handled. When filter returns empty
    # but PR has stack metadata, evaluate_guard still retains via metadata.
    open_pulls, open_pulls_error = fetch_open_pulls(
        repo=repo,
        http_get=getter,
        api_version=api_version,
    )
    return evaluate_guard(
        repo=repo,
        pr_number=pr_number,
        head_branch=head_branch,
        stack_metadata=stack_metadata,
        stacks=stacks,
        stacks_error=stacks_error,
        open_pulls=open_pulls,
        open_pulls_error=open_pulls_error,
    )


def _load_stack_metadata_arg(raw: str | None) -> Any:
    if raw is None:
        return None
    text = raw.strip()
    if not text or text in ("null", "undefined", "None"):
        return None
    # Allow passing a path to a JSON file via @path
    if text.startswith("@"):
        path = text[1:]
        try:
            file_text = Path(path).read_text(encoding="utf-8").strip()
        except OSError as exc:
            # Unreadable file → fail closed via malformed string path
            return {"__malformed__": f"unreadable stack metadata file: {exc}"}
        if not file_text or file_text in ("null", "undefined", "None"):
            return None
        try:
            return json.loads(file_text)
        except json.JSONDecodeError as exc:
            return {"__malformed__": f"stack metadata file is not valid JSON: {exc}"}
    try:
        return json.loads(text)
    except json.JSONDecodeError:
        # Leave as string; parse_stack_metadata will classify
        return text


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Fail-closed guard for closed-pr-cleanup under native stacked PRs"
    )
    parser.add_argument("--repo", required=True, help="owner/name")
    parser.add_argument("--pr", type=int, required=True, help="closed pull request number")
    parser.add_argument("--head-branch", required=True, help="closed PR head branch name")
    parser.add_argument(
        "--stack-metadata",
        default=None,
        help='PR .stack JSON, JSON string, or @file path (optional)',
    )
    parser.add_argument(
        "--output",
        choices=("text", "json"),
        default="text",
        help="decision output format",
    )
    parser.add_argument(
        "--github-output",
        default=None,
        help="If set, append eligible_for_cleanup=<bool> to this file (GITHUB_OUTPUT)",
    )
    args = parser.parse_args([] if argv is None else argv)

    stack_metadata = _load_stack_metadata_arg(args.stack_metadata)
    decision = run_guard(
        repo=args.repo,
        pr_number=args.pr,
        head_branch=args.head_branch,
        stack_metadata=stack_metadata,
    )

    if args.output == "json":
        print(json.dumps(decision.to_public_dict(), indent=2, sort_keys=True))
    else:
        status = "ELIGIBLE" if decision.eligible_for_cleanup else "RETAIN"
        print(f"closed-pr-cleanup-guard: {status}: {decision.reason}")

    if args.github_output:
        with open(args.github_output, "a", encoding="utf-8") as handle:
            handle.write(
                f"eligible_for_cleanup={'true' if decision.eligible_for_cleanup else 'false'}\n"
            )
            # Multiline reason for logs / optional consumers
            reason_escaped = decision.reason.replace("%", "%25").replace("\n", "%0A")
            handle.write(f"reason={reason_escaped}\n")

    # Exit 0 always when evaluation completed: retention is not a hard failure.
    # Callers gate destructive steps on eligible_for_cleanup output.
    return 0


if __name__ == "__main__":
    sys.exit(main())
