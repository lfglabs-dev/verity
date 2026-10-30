import fnmatch
import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WORKFLOW = ROOT / ".github" / "workflows" / "evmyullean-fork-conformance.yml"
TRUST_ASSUMPTIONS = ROOT / "docs" / "TRUST_ASSUMPTIONS.md"
AXIOMS = ROOT / "docs" / "AXIOMS.md"
MAKEFILE = ROOT / "Makefile"
NATIVE_LOWERING_REPORT = ROOT / "artifacts" / "evmyullean_native_lowering_report.json"
ROADMAP = ROOT / "docs" / "ROADMAP.md"


class EvmYulLeanForkConformanceWorkflowTests(unittest.TestCase):
    def test_concrete_bridge_test_count_matches_native_lowering_report(self) -> None:
        report = json.loads(NATIVE_LOWERING_REPORT.read_text(encoding="utf-8"))
        count = report["concrete_test_count"]
        test_count_re = re.compile(
            r"\b(\d+)\s+(?:concrete\s+)?(?:`native_decide`\s+|native_decide\s+)?"
            r"bridge(?:-equivalence)?\s+tests\b",
        )

        for path in [MAKEFILE, WORKFLOW, TRUST_ASSUMPTIONS, ROADMAP]:
            text = path.read_text(encoding="utf-8")
            normalized_text = re.sub(r"(?m)^\s*#\s?", "", text)
            normalized_text = re.sub(r"\s+", " ", normalized_text)
            documented_counts = {int(match) for match in test_count_re.findall(normalized_text)}
            self.assertIn(
                count,
                documented_counts,
                f"{path.relative_to(ROOT)} should document the generated concrete bridge-test count",
            )
            self.assertEqual(
                {count},
                documented_counts,
                f"{path.relative_to(ROOT)} should not contain stale concrete bridge-test counts",
            )

    def test_scheduled_failures_open_or_update_issue(self) -> None:
        text = WORKFLOW.read_text(encoding="utf-8")

        # The burn-in window ended 2026-05-04; the workflow now fails hard on
        # any probe failure and the drift issue is unconditionally opened or
        # updated for scheduled/manual runs.
        self.assertNotIn("BURN_IN_END_UTC", text)
        self.assertNotIn("burn-in", text)
        self.assertNotIn("burnInEnd", text)
        self.assertNotIn("continue-on-error", text)
        for path in [
            "Compiler/Proofs/EndToEnd.lean",
            "Compiler/Proofs/EndToEnd/**",
            "Compiler/Proofs/YulGeneration/Backends/**",
            "scripts/generate_evmyullean_native_lowering_report.py",
            "scripts/test_evmyullean_fork_conformance_workflow.py",
            "artifacts/evmyullean_native_lowering_report.json",
            "lake-manifest.json",
            "lean-toolchain",
        ]:
            self.assertEqual(
                text.count(path),
                2,
                f"{path} should trigger both push and pull_request probes",
            )

        push_paths_match = re.search(
            r"(?m)^  push:\n(?:    .+\n)*?    paths:\n(?P<paths>(?:      - '.+'\n)+)",
            text,
        )
        pr_paths_match = re.search(
            r"(?m)^  pull_request:\n(?:    .+\n)*?    paths:\n(?P<paths>(?:      - '.+'\n)+)",
            text,
        )
        self.assertIsNotNone(push_paths_match)
        self.assertIsNotNone(pr_paths_match)
        push_globs = re.findall(r"- '([^']+)'", push_paths_match.group("paths"))
        pr_globs = re.findall(r"- '([^']+)'", pr_paths_match.group("paths"))
        self.assertEqual(push_globs, pr_globs)

        def matches_any_workflow_glob(rel_path: str, globs: list[str]) -> bool:
            for pattern in globs:
                if pattern.endswith("/**"):
                    prefix = pattern[:-2]
                    if rel_path.startswith(prefix):
                        return True
                elif fnmatch.fnmatch(rel_path, pattern):
                    return True
            return False

        import_re = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)", re.M)
        seed_modules = [
            "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas",
            "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeTest",
            "Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness",
            "Compiler.Proofs.EndToEnd",
        ]
        seen_modules: set[str] = set()
        queue = list(seed_modules)
        while queue:
            mod = queue.pop(0)
            if mod in seen_modules:
                continue
            seen_modules.add(mod)
            mod_path = ROOT / (mod.replace(".", "/") + ".lean")
            if not mod_path.exists():
                continue
            for imported in import_re.findall(mod_path.read_text(encoding="utf-8")):
                if imported not in seen_modules:
                    queue.append(imported)

        for mod in sorted(seen_modules):
            rel = mod.replace(".", "/") + ".lean"
            if (
                rel.startswith("Compiler/Proofs/YulGeneration/Backends/")
                or rel.startswith("Compiler/Proofs/EndToEnd")
            ) and (ROOT / rel).exists():
                self.assertTrue(
                    matches_any_workflow_glob(rel, push_globs),
                    f"Transitive probe dependency {rel} is not covered by workflow path filters",
                )

        top_permissions = re.search(
            r"(?m)^permissions:\n(?P<body>(?:  .+\n)+)\n(?:env:|concurrency:|jobs:)",
            text,
        )
        self.assertIsNotNone(top_permissions)
        self.assertIn("  contents: read", top_permissions.group("body"))
        self.assertNotIn("issues: write", top_permissions.group("body"))

        issue_job = re.search(
            r"(?m)^  open-drift-issue:\n(?P<body>.*?)(?=\n  [A-Za-z0-9_-]+:|\Z)",
            text,
            re.S,
        )
        self.assertIsNotNone(issue_job)
        issue_job_body = issue_job.group("body")
        self.assertIn("needs: probe", issue_job_body)
        self.assertIn("needs.probe.result == 'failure'", issue_job_body)
        self.assertIn("github.event_name == 'schedule'", issue_job_body)
        self.assertIn("github.event_name == 'workflow_dispatch'", issue_job_body)
        self.assertNotIn("github.event_name == 'pull_request'", issue_job_body)
        self.assertNotIn("github.event_name == 'push'", issue_job_body)
        self.assertIn("issues: write", issue_job_body)
        self.assertIn("uses: actions/github-script@f28e40c7f34bde8b3046d885e986cb6290c5673b", text)
        self.assertIn("const title = \"EVMYulLean fork conformance probe failed\";", text)
        self.assertIn("github.rest.issues.createComment", text)
        self.assertIn("github.rest.issues.create({", text)
        self.assertIn("make test-evmyullean-fork", text)
        makefile_text = MAKEFILE.read_text(encoding="utf-8")
        self.assertIn("python3 scripts/generate_evmyullean_native_lowering_report.py --check", makefile_text)
        self.assertIn("lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanNativeHarness", makefile_text)
        self.assertIn("lake build Compiler.Proofs.EndToEnd", makefile_text)

        issue_step = re.search(
            r"- name: Open or update drift issue\n(?P<body>.*?)(?=\n      - name:|\Z)",
            text,
            re.S,
        )
        self.assertIsNotNone(issue_step)

    def test_trust_assumptions_describe_scheduled_issue_path(self) -> None:
        text = TRUST_ASSUMPTIONS.read_text(encoding="utf-8")
        self.assertIn("weekly scheduled GitHub Actions workflow", text)
        self.assertIn("automatically opened or updated GitHub issue", text)
        self.assertNotIn("burn-in", text)

    def test_axioms_document_non_axiom_evmyullean_controls(self) -> None:
        text = AXIOMS.read_text(encoding="utf-8")
        self.assertIn("## EVMYulLean Runtime Semantics (Non-Axiom)", text)
        self.assertIn("make test-evmyullean-fork", text)
        self.assertIn(".github/workflows/evmyullean-fork-conformance.yml", text)
        self.assertIn("open or update a GitHub issue", text)
        self.assertNotIn("burn-in", text)


if __name__ == "__main__":
    unittest.main()
