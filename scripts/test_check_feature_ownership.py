#!/usr/bin/env python3
"""Unit tests for check_feature_ownership.py."""

from __future__ import annotations

import json
import io
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import check_feature_ownership as check


class FeatureOwnershipTests(unittest.TestCase):
    def test_repository_artifact_passes(self) -> None:
        subprocess.run([sys.executable, "scripts/check_feature_ownership.py"], check=True)

    def test_missing_required_surface_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "feature_ownership.json"
            path.write_text(
                json.dumps(
                    {
                        "status_values": ["supported", "partial", "unsupported", "not_applicable"],
                        "surfaces": [],
                    }
                ),
                encoding="utf-8",
            )
            old_artifact = check.ARTIFACT
            check.ARTIFACT = path
            try:
                with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    check.main()
            finally:
                check.ARTIFACT = old_artifact


if __name__ == "__main__":
    unittest.main()
