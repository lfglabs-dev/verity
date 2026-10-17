#!/usr/bin/env python3
"""Unit tests for scripts/lean_repl_daemon.py using a mock REPL process."""

from __future__ import annotations

import json
import os
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import lean_repl_daemon


MOCK_REPL_CODE = """#!/usr/bin/env python3
import json
import sys

env_counter = 0
lines = []
for line in sys.stdin:
    if line in ("\\n", "\\r\\n"):
        if not lines:
            continue
        req = json.loads("".join(lines))
        lines = []
        cmd = req.get("cmd", "")
        messages = []
        if "FAIL_HERE" in cmd:
            messages.append({"severity": "error", "data": "synthetic error"})
        resp = {"env": env_counter, "messages": messages, "received_env": req.get("env")}
        env_counter += 1
        sys.stdout.write(json.dumps(resp) + "\\n\\n")
        sys.stdout.flush()
    else:
        lines.append(line)
"""


class LeanReplDaemonTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.socket_path = self.root / "repl.sock"
        self.mock_repl = self.root / "mock_repl.py"
        self.mock_repl.write_text(MOCK_REPL_CODE, encoding="utf-8")
        self.mock_repl.chmod(self.mock_repl.stat().st_mode | stat.S_IEXEC)

    def tearDown(self) -> None:
        try:
            lean_repl_daemon.main(["stop", "--socket", str(self.socket_path)])
        except Exception:
            pass
        self.tempdir.cleanup()

    def test_extract_import_header_and_slice(self) -> None:
        sample = self.root / "Sample.lean"
        sample.write_text(
            "import Std\nopen Classical\n\ndef foo : Nat := 1\ntheorem bar : foo = 1 := rfl\n",
            encoding="utf-8",
        )
        header = lean_repl_daemon.extract_import_header(sample, None)
        self.assertEqual(header.strip(), "import Std\nopen Classical")
        sliced = lean_repl_daemon.extract_file_slice(sample, 4, 5)
        self.assertIn("def foo : Nat := 1", sliced)
        self.assertIn("theorem bar : foo = 1 := rfl", sliced)

    def test_persistent_daemon_preserves_header_env_across_invocations(self) -> None:
        sample = self.root / "Sample.lean"
        sample.write_text(
            "import Std\nopen Classical\n\ndef foo : Nat := 1\ntheorem bar : foo = 1 := rfl\n",
            encoding="utf-8",
        )
        rc = lean_repl_daemon.main(
            [
                "start",
                "--socket",
                str(self.socket_path),
                "--repl-bin",
                str(self.mock_repl),
                "--cwd",
                str(self.root),
                "--no-lake-env",
            ]
        )
        self.assertEqual(rc, 0)

        rc_header = lean_repl_daemon.main(
            [
                "load-header",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--until-line",
                "2",
            ]
        )
        self.assertEqual(rc_header, 0)

        status = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})
        self.assertEqual(status["header_env"], 0)

        rc_check = lean_repl_daemon.main(
            [
                "check",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--start-line",
                "4",
                "--end-line",
                "5",
            ]
        )
        self.assertEqual(rc_check, 0)

        sample.write_text(
            "import Std\nopen Classical\n\ndef foo : Nat := FAIL_HERE\n",
            encoding="utf-8",
        )
        rc_fail = lean_repl_daemon.main(
            [
                "check",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--start-line",
                "4",
                "--end-line",
                "4",
            ]
        )
        self.assertEqual(rc_fail, 1)


if __name__ == "__main__":
    unittest.main()
