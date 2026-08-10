#!/usr/bin/env python3
"""Regression tests for self-hosted runner class provisioning."""

from __future__ import annotations

import re
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("install_self_hosted_runner.sh")


def host_case(text: str, selector: str) -> str:
    match = re.search(
        rf"^  {re.escape(selector)}\)\n(?P<body>.*?)(?=^  [^ ]+\)\n|^esac$)",
        text,
        flags=re.MULTILINE | re.DOTALL,
    )
    if match is None:
        raise AssertionError(f"missing host selector: {selector}")
    return match.group("body")


class RunnerProvisioningLabelsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.script = SCRIPT.read_text(encoding="utf-8")

    def test_fricobackend_is_heavy_and_medium(self) -> None:
        body = host_case(self.script, "88.99.4.254|healthy-build")
        self.assertIn("build-heavy", body)
        self.assertIn("build-medium", body)

    def test_ashur_is_medium_only(self) -> None:
        body = host_case(self.script, "188.40.69.160|ashur-medium")
        self.assertIn("build-medium", body)
        self.assertNotIn("build-heavy", body)

    def test_old_agent_is_medium_only(self) -> None:
        body = host_case(self.script, "95.216.112.253|old-agent-medium")
        self.assertIn("build-medium", body)
        self.assertNotIn("build-heavy", body)

    def test_nippur_is_medium_only(self) -> None:
        body = host_case(self.script, "37.187.92.183|nippur-medium")
        self.assertIn("build-medium", body)
        self.assertNotIn("build-heavy", body)
        self.assertIn("mem-28g", body)

    def test_generic_heavy_runners_are_medium_fallbacks(self) -> None:
        generic = self.script.split("    *)\n      case \"$1\" in", 1)[1]
        self.assertIn("build-heavy,build-medium", generic)


if __name__ == "__main__":
    unittest.main()
