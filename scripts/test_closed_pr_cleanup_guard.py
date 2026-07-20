#!/usr/bin/env python3
"""Deterministic tests for closed_pr_cleanup_guard (native stack fail-closed)."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
import unittest.mock
from pathlib import Path
from typing import Any, Mapping

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import closed_pr_cleanup_guard as guard


FIXTURES = SCRIPT_DIR / "fixtures" / "closed_pr_cleanup_guard"


def _load_fixture(name: str) -> Any:
    path = FIXTURES / name
    return json.loads(path.read_text(encoding="utf-8"))


class ParseMetadataTests(unittest.TestCase):
    def test_absent_null_metadata(self) -> None:
        obj, err = guard.parse_stack_metadata(None)
        self.assertIsNone(obj)
        self.assertIsNone(err)
        obj, err = guard.parse_stack_metadata("null")
        self.assertIsNone(obj)
        self.assertIsNotNone(err)

    def test_empty_and_malformed_metadata(self) -> None:
        obj, err = guard.parse_stack_metadata({})
        self.assertIsNone(obj)
        self.assertIsNotNone(err)
        self.assertIn("empty", err.lower())

        obj, err = guard.parse_stack_metadata("")
        self.assertIsNone(obj)
        self.assertIsNotNone(err)

        obj, err = guard.parse_stack_metadata("not-json{")
        self.assertIsNone(obj)
        self.assertIsNotNone(err)

        obj, err = guard.parse_stack_metadata([])
        self.assertIsNone(obj)
        self.assertIsNotNone(err)

        obj, err = guard.parse_stack_metadata({"foo": 1})
        self.assertIsNone(obj)
        self.assertIsNotNone(err)
        self.assertIn("id/number", err)

    def test_well_formed_metadata(self) -> None:
        raw = _load_fixture("stack_metadata_member.json")
        obj, err = guard.parse_stack_metadata(raw)
        self.assertIsNone(err)
        assert obj is not None
        self.assertEqual(obj["size"], 3)
        self.assertEqual(obj["position"], 2)


class EvaluateGuardTests(unittest.TestCase):
    def test_stack_peer_with_empty_merged_at_is_retained(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=1,
            head_branch="closed-base",
            stacks=[{
                "open": False,
                "pull_requests": [
                    {"number": 1, "state": "closed", "merged_at": None,
                     "head": {"ref": "closed-base"}},
                    {"number": 2, "state": "open", "merged_at": "",
                     "head": {"ref": "dependent"}},
                ],
            }],
            open_pulls=[],
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(any("native stack" in reason for reason in decision.retain_reasons))

    def test_standalone_closed_pr_eligible(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata=None,
            stacks=[],
            stacks_error=None,
            open_pulls=_load_fixture("open_pulls_no_dependents.json"),
            open_pulls_error=None,
        )
        self.assertTrue(decision.eligible_for_cleanup)
        self.assertTrue(decision.reason.startswith("eligible:"))
        self.assertEqual(decision.retain_reasons, ())

    def test_native_stack_member_must_be_retained(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=2172,
            head_branch="codex/2080-direct-helper-fuel-split-consumer",
            stack_metadata=_load_fixture("stack_metadata_member.json"),
            stacks=_load_fixture("stacks_open_with_member.json"),
            stacks_error=None,
            open_pulls=_load_fixture("open_pulls_no_dependents.json"),
            open_pulls_error=None,
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(
            any("stack member" in r.lower() or "native stack" in r.lower() for r in decision.retain_reasons)
        )

    def test_branch_used_as_base_by_open_dependent_must_be_retained(self) -> None:
        # #2173 failure mode: closed PR head is still base of an open dependent.
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=2172,
            head_branch="codex/2080-direct-helper-fuel-split-consumer",
            stack_metadata=None,
            stacks=[],
            stacks_error=None,
            open_pulls=_load_fixture("open_pulls_with_dependent.json"),
            open_pulls_error=None,
        )
        self.assertFalse(decision.eligible_for_cleanup)
        joined = " ".join(decision.retain_reasons).lower()
        self.assertIn("dependent", joined)
        self.assertIn("#2173", " ".join(decision.retain_reasons))

    def test_stacks_api_unavailable_fail_closed(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata=None,
            stacks=None,
            stacks_error="stacks API returned HTTP 503",
            open_pulls=_load_fixture("open_pulls_no_dependents.json"),
            open_pulls_error=None,
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(
            any("stacks api unavailable" in r.lower() for r in decision.retain_reasons)
        )

    def test_stacks_api_ambiguous_empty_error_fail_closed(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata=None,
            stacks=None,
            stacks_error=None,  # missing result without error → ambiguous
            open_pulls=[],
            open_pulls_error=None,
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(any("ambiguous" in r.lower() for r in decision.retain_reasons))

    def test_malformed_empty_metadata_fail_closed(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata={},
            stacks=[],
            open_pulls=[],
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(any("empty" in r.lower() for r in decision.retain_reasons))

    def test_dependent_check_unavailable_fail_closed(self) -> None:
        decision = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata=None,
            stacks=[],
            open_pulls=None,
            open_pulls_error="pulls API returned HTTP 500",
        )
        self.assertFalse(decision.eligible_for_cleanup)
        self.assertTrue(
            any("dependent pr check unavailable" in r.lower() for r in decision.retain_reasons)
        )

    def test_malformed_branch_and_pr(self) -> None:
        d1 = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=0,
            head_branch="x",
            stacks=[],
            open_pulls=[],
        )
        self.assertFalse(d1.eligible_for_cleanup)
        d2 = guard.evaluate_guard(
            repo="lfglabs-dev/verity",
            pr_number=1,
            head_branch="   ",
            stacks=[],
            open_pulls=[],
        )
        self.assertFalse(d2.eligible_for_cleanup)


class HttpIntegrationTests(unittest.TestCase):
    def test_stacks_pagination_and_later_error(self) -> None:
        calls: list[str] = []

        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            calls.append(url)
            if "&page=1&" in url:
                return 200, json.dumps([{"open": False, "pull_requests": []}])
            return 503, '{"message":"unavailable"}'

        stacks, err = guard.fetch_stacks(
            repo="lfglabs-dev/verity", pull_request=2172, http_get=http_get, per_page=1
        )
        self.assertIsNone(stacks)
        self.assertIn("page 2", err or "")
        self.assertEqual(len(calls), 2)

    def test_event_metadata_absent_vs_present_null(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            event = Path(tmp) / "event.json"
            event.write_text('{"pull_request": {}}', encoding="utf-8")
            self.assertIsNone(guard._load_stack_metadata_from_event(str(event)))
            event.write_text('{"pull_request": {"stack": null}}', encoding="utf-8")
            loaded = guard._load_stack_metadata_from_event(str(event))
            decision = guard.evaluate_guard(
                repo="lfglabs-dev/verity", pr_number=1, head_branch="x",
                stack_metadata=loaded, stacks=[], open_pulls=[]
            )
            self.assertFalse(decision.eligible_for_cleanup)

    def test_draft_dependent_is_open_and_retained(self) -> None:
        pulls = [{"number": 2, "state": "open", "draft": True, "base": {"ref": "base"}}]
        self.assertEqual(
            guard.open_dependents_on_branch(pulls, head_branch="base", closed_pr_number=1),
            [2],
        )

    def test_run_guard_with_injected_http(self) -> None:
        stacks_body = json.dumps(_load_fixture("stacks_open_with_member.json"))
        pulls_body = json.dumps(_load_fixture("open_pulls_with_dependent.json"))

        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            if "/stacks" in url:
                return 200, stacks_body
            if "/pulls" in url:
                return 200, pulls_body
            return 404, '{"message":"not found"}'

        decision = guard.run_guard(
            repo="lfglabs-dev/verity",
            pr_number=2172,
            head_branch="codex/2080-direct-helper-fuel-split-consumer",
            stack_metadata=None,
            http_get=http_get,
        )
        self.assertFalse(decision.eligible_for_cleanup)

    def test_run_guard_stacks_404_means_not_enabled_standalone_ok(self) -> None:
        """404 on /stacks = preview not enabled; do not weaken standalone cleanup."""
        pulls_body = json.dumps(_load_fixture("open_pulls_no_dependents.json"))

        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            if "/stacks" in url:
                return 404, '{"message":"Not Found"}'
            if "/pulls" in url:
                return 200, pulls_body
            return 500, "err"

        decision = guard.run_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            http_get=http_get,
        )
        self.assertTrue(decision.eligible_for_cleanup)

    def test_run_guard_stacks_503_fail_closed(self) -> None:
        pulls_body = json.dumps(_load_fixture("open_pulls_no_dependents.json"))

        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            if "/stacks" in url:
                return 503, '{"message":"unavailable"}'
            if "/pulls" in url:
                return 200, pulls_body
            return 500, "err"

        decision = guard.run_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            http_get=http_get,
        )
        self.assertFalse(decision.eligible_for_cleanup)

    def test_run_guard_standalone_eligible_via_http(self) -> None:
        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            if "/stacks" in url:
                return 200, "[]"
            if "/pulls" in url:
                return 200, json.dumps(_load_fixture("open_pulls_no_dependents.json"))
            return 404, "{}"

        decision = guard.run_guard(
            repo="lfglabs-dev/verity",
            pr_number=100,
            head_branch="feature/standalone",
            stack_metadata=None,
            http_get=http_get,
        )
        self.assertTrue(decision.eligible_for_cleanup)

    def test_main_writes_github_output(self) -> None:
        pulls_body = json.dumps(_load_fixture("open_pulls_no_dependents.json"))

        def http_get(url: str, headers: Mapping[str, str]) -> tuple[int, str]:
            del headers
            if "/stacks" in url:
                return 200, "[]"
            if "/pulls" in url:
                return 200, pulls_body
            return 404, "{}"

        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "github_output"
            with unittest.mock.patch.object(guard, "default_http_getter", return_value=http_get):
                rc = guard.main(
                    [
                        "--repo",
                        "lfglabs-dev/verity",
                        "--pr",
                        "100",
                        "--head-branch",
                        "feature/standalone",
                        "--github-output",
                        str(out),
                        "--output",
                        "json",
                    ]
                )
            self.assertEqual(rc, 0)
            text = out.read_text(encoding="utf-8")
            self.assertIn("eligible_for_cleanup=true", text)


class PayloadParseTests(unittest.TestCase):
    def test_stacks_payload_malformed(self) -> None:
        stacks, err = guard.parse_stacks_list_payload("")
        self.assertIsNone(stacks)
        self.assertIsNotNone(err)
        stacks, err = guard.parse_stacks_list_payload('{"nope": true}')
        self.assertIsNone(stacks)
        self.assertIsNotNone(err)
        stacks, err = guard.parse_stacks_list_payload("[]")
        self.assertEqual(stacks, [])
        self.assertIsNone(err)

    def test_pulls_payload_malformed(self) -> None:
        pulls, err = guard.parse_pulls_list_payload("{}")
        self.assertIsNone(pulls)
        self.assertIsNotNone(err)


if __name__ == "__main__":
    unittest.main()
