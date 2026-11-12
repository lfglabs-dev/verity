#!/usr/bin/env python3
from __future__ import annotations

import io
import sys
import tempfile
import textwrap
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_docs_workflow_sync as check


class CheckDocsWorkflowSyncTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory(dir=SCRIPT_DIR.parent)
        self.root = Path(self.tempdir.name)
        self.workflow = self.root / ".github" / "workflows" / "docs.yml"
        self.workflow.parent.mkdir(parents=True, exist_ok=True)

        self.old_root = check.ROOT
        self.old_workflow = check.DOCS_WORKFLOW
        self.old_workflows_dir = check.WORKFLOWS_DIR
        self.old_runners_doc = check.CI_RUNNERS_DOC
        check.ROOT = self.root
        check.DOCS_WORKFLOW = self.workflow
        check.WORKFLOWS_DIR = self.workflow.parent
        check.CI_RUNNERS_DOC = self.root / "docs" / "CI_RUNNERS.md"

    def tearDown(self) -> None:
        check.ROOT = self.old_root
        check.DOCS_WORKFLOW = self.old_workflow
        check.WORKFLOWS_DIR = self.old_workflows_dir
        check.CI_RUNNERS_DOC = self.old_runners_doc
        self.tempdir.cleanup()

    def _write_workflow(self, text: str) -> None:
        self.workflow.write_text(textwrap.dedent(text).lstrip(), encoding="utf-8")

    def _write_runners_doc(self, text: str) -> Path:
        doc = self.root / "docs" / "CI_RUNNERS.md"
        doc.parent.mkdir(parents=True, exist_ok=True)
        doc.write_text(textwrap.dedent(text).lstrip(), encoding="utf-8")
        return doc

    def test_check_passes_for_expected_paths(self) -> None:
        self._write_workflow(
            """
            name: Docs
            on:
              push:
                branches: [main]
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
              pull_request:
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: npm run build
            """
        )

        self.assertEqual(check.check_docs_workflow_sync(self.workflow), 0)

    def test_check_fails_when_workflow_file_is_missing_from_push_paths(self) -> None:
        self._write_workflow(
            """
            name: Docs
            on:
              push:
                branches: [main]
                paths:
                  - 'docs-site/**'
              pull_request:
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: npm run build
            """
        )

        stderr = io.StringIO()
        with redirect_stderr(stderr):
            rc = check.check_docs_workflow_sync(self.workflow)

        self.assertEqual(rc, 1)
        self.assertIn("on.push.paths does not match expected paths.", stderr.getvalue())

    def test_main_fails_when_push_and_pull_request_paths_diverge(self) -> None:
        self._write_workflow(
            """
            name: Docs
            on:
              push:
                branches: [main]
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
              pull_request:
                paths:
                  - 'docs-site/**'
                  - '.github/workflows/docs.yml'
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: npm run build
            """
        )

        old_argv = sys.argv
        sys.argv = ["check_docs_workflow_sync.py"]
        try:
            stderr = io.StringIO()
            stdout = io.StringIO()
            with redirect_stderr(stderr), redirect_stdout(stdout):
                rc = check.main()
        finally:
            sys.argv = old_argv

        self.assertEqual(rc, 1)
        self.assertIn("on.push.paths does not match on.pull_request.paths.", stderr.getvalue())

    def test_check_passes_when_ci_runners_doc_matches_workflow_targets(self) -> None:
        self._write_workflow(
            """
            name: Docs
            on:
              push:
                branches: [main]
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
              pull_request:
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: npm run build
            """
        )
        (self.workflow.parent / "verify.yml").write_text(
            textwrap.dedent(
                """
                name: Verify
                jobs:
                  build:
                    runs-on: lean-16vcpu-ubuntu-2604
                    steps: []
                  benchmark:
                    runs-on: ${{ fromJSON(inputs.runner_labels_json) }}
                    steps: []
                """
            ).lstrip(),
            encoding="utf-8",
        )
        doc = self._write_runners_doc(
            """
            # Verity CI Runner Architecture

            ```yaml
            runs-on: ubuntu-latest
            runs-on: lean-16vcpu-ubuntu-2604
            ```
            """
        )

        self.assertEqual(
            check.check_docs_workflow_sync(
                self.workflow,
                runners_doc_path=doc,
                workflows_dir=self.workflow.parent,
            ),
            0,
        )

    def test_check_fails_when_ci_runners_doc_drifts_from_workflow_targets(self) -> None:
        self._write_workflow(
            """
            name: Docs
            on:
              push:
                branches: [main]
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
              pull_request:
                paths:
                  - '.github/workflows/docs.yml'
                  - 'docs-site/**'
            jobs:
              build:
                runs-on: ubuntu-latest
                steps:
                  - run: npm run build
            """
        )
        (self.workflow.parent / "verify.yml").write_text(
            textwrap.dedent(
                """
                name: Verify
                jobs:
                  build:
                    runs-on: lean-16vcpu-ubuntu-2604
                    steps: []
                """
            ).lstrip(),
            encoding="utf-8",
        )
        doc = self._write_runners_doc(
            """
            # Verity CI Runner Architecture

            ```yaml
            runs-on: ubuntu-latest
            runs-on: [self-hosted, linux, x64, verity, build, build-medium]
            ```
            """
        )

        stderr = io.StringIO()
        with redirect_stderr(stderr):
            rc = check.check_docs_workflow_sync(
                self.workflow,
                runners_doc_path=doc,
                workflows_dir=self.workflow.parent,
            )

        self.assertEqual(rc, 1)
        self.assertIn(
            "docs/CI_RUNNERS.md runs-on targets does not match workflow runs-on targets.",
            stderr.getvalue(),
        )


if __name__ == "__main__":
    unittest.main()
