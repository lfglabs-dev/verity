#!/usr/bin/env python3
"""Offline controls for check_importer_move_equivalence.py (#2837).

No Lean runs here. The comparator is exercised on synthetic dumps shaped like
the real ones, target discovery and probe generation on the in-tree smoke
modules, and the anchor check on the in-tree mutation scripts plus synthetic
negative controls.
"""
from __future__ import annotations

import contextlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_importer_move_equivalence as harness
from check_importer_move_equivalence import Anchor, HarnessError

DIGEST_A = "a" * 64
DIGEST_B = "b" * 64


def report(digest: str, contract: str = "C", sha: str = "1" * 64) -> str:
    return (f'{{ importerVersion := "v", solcLongVersion := "0.8.34", solcSha256 := "{sha}",\n'
            f'  settingsJson := "{{}}", sourceDigest := "{digest}", contract := "{contract}",\n'
            f'  roots := ["f()"], functions := [] }}\n')


def model(body: str = "x") -> str:
    return f'{{ name := "C", functions := [{{ name := "f", body := [{body}] }}] }}\n'


def write_dump(directory: Path, imports: dict[str, dict[str, str]], diagnostics: dict[str, str] | None = None,
               exits: dict[str, str] | None = None, targets: dict | None = None,
               incomplete: tuple[str, ...] = (), **manifest_fields) -> Path:
    """A dump laid out as `dump` writes it. `imports` maps module -> {file name: text}."""
    directory.mkdir(parents=True)
    manifest_targets = {}
    for module, files in imports.items():
        (directory / module).mkdir()
        for name, text in files.items():
            (directory / module / name).write_text(text)
        (directory / module / "diagnostics.txt").write_text((diagnostics or {}).get(module, ""))
        (directory / module / "exit").write_text((exits or {}).get(module, "0\n"))
        if module not in (incomplete or ()):
            (directory / module / "complete").write_text("")
        manifest_targets[module] = sorted({name.rsplit(".", 1)[0] for name in files})
    (directory / "probes").mkdir()
    (directory / "probes" / "ignored.lean").write_text("-- probes are not compared\n")
    manifest = {"revision": directory.name, "dirty": False, "built": True,
                "targets": targets or manifest_targets, **manifest_fields}
    (directory / "manifest.json").write_text(json.dumps(manifest))
    return directory


def two_imports(digest: str = DIGEST_A, second_model: str = "y") -> dict[str, dict[str, str]]:
    return {"ModuleA": {"N.one.model": model("x"), "N.one.report": report(digest),
                        "N.two.model": model(second_model), "N.two.report": report(digest, "D")},
            "ModuleB": {"N.three.report": report(digest)}}


class CompareTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def compare(self, base: dict, candidate: dict, **kwargs) -> dict:
        base_kwargs = {k[5:]: v for k, v in kwargs.items() if k.startswith("base_")}
        cand_kwargs = {k[5:]: v for k, v in kwargs.items() if k.startswith("cand_")}
        return harness.compare(write_dump(self.dir / "base", base, **base_kwargs),
                               write_dump(self.dir / "cand", candidate, **cand_kwargs))

    def test_identical_dumps_match_and_count_every_kind(self) -> None:
        summary = self.compare(two_imports(), two_imports())
        self.assertEqual(summary["mismatches"], [])
        self.assertEqual(summary["compared"], {"model": 2, "report": 3, "diagnostics": 2, "exit": 2, "complete": 2})
        self.assertEqual(summary["reports_with_changed_digest"], 0)

    def test_digest_only_difference_is_allowed_and_counted(self) -> None:
        summary = self.compare(two_imports(DIGEST_A), two_imports(DIGEST_B))
        self.assertEqual(summary["mismatches"], [])
        self.assertEqual(summary["reports_with_changed_digest"], 3)

    def test_model_difference_fails(self) -> None:
        summary = self.compare(two_imports(), two_imports(second_model="z"))
        self.assertEqual(summary["mismatches"], ["differs: ModuleA/N.two.model"])

    def test_swapped_models_fail(self) -> None:
        base = two_imports()
        candidate = two_imports()
        a = candidate["ModuleA"]
        a["N.one.model"], a["N.two.model"] = a["N.two.model"], a["N.one.model"]
        summary = self.compare(base, candidate)
        self.assertEqual(summary["mismatches"], ["differs: ModuleA/N.one.model", "differs: ModuleA/N.two.model"])

    def test_report_difference_outside_digest_fails(self) -> None:
        candidate = two_imports(DIGEST_B)
        candidate["ModuleB"]["N.three.report"] = report(DIGEST_B, contract="E")
        summary = self.compare(two_imports(DIGEST_A), candidate)
        self.assertEqual(summary["mismatches"], ["differs: ModuleB/N.three.report"])

    def test_other_64_hex_report_fields_are_not_masked(self) -> None:
        candidate = two_imports()
        candidate["ModuleB"]["N.three.report"] = report(DIGEST_A, sha="2" * 64)
        summary = self.compare(two_imports(), candidate)
        self.assertEqual(summary["mismatches"], ["differs: ModuleB/N.three.report"])

    def test_diagnostic_difference_fails(self) -> None:
        line = "<out>/probes/ModuleA.lean:3:0: warning: [solidity-import:unsupported] f: x\n"
        summary = self.compare(two_imports(), two_imports(), base_diagnostics={"ModuleA": line},
                               cand_diagnostics={"ModuleA": line.replace("f: x", "f: y")})
        self.assertEqual(summary["mismatches"], ["differs: ModuleA/diagnostics.txt"])

    def test_digest_in_diagnostics_is_not_masked(self) -> None:
        summary = self.compare(two_imports(), two_imports(), base_diagnostics={"ModuleB": f"digest {DIGEST_A}\n"},
                               cand_diagnostics={"ModuleB": f"digest {DIGEST_B}\n"})
        self.assertEqual(summary["mismatches"], ["differs: ModuleB/diagnostics.txt"])

    def test_exit_code_difference_fails(self) -> None:
        summary = self.compare(two_imports(), two_imports(), cand_exits={"ModuleB": "1\n"})
        self.assertEqual(summary["mismatches"], ["differs: ModuleB/exit"])

    def test_identical_kill_of_all_guarded_module_fails(self) -> None:
        imports = {"ModuleA": two_imports()["ModuleA"], "Guarded": {}}
        targets = {"ModuleA": ["N.one", "N.two"], "Guarded": ["N.rejected"]}
        guarded = {"Guarded": ["N.rejected"]}
        summary = self.compare(imports, imports, base_targets=targets, cand_targets=targets,
                               base_guarded=guarded, cand_guarded=guarded,
                               base_exits={"Guarded": "137\n"}, cand_exits={"Guarded": "137\n"},
                               base_incomplete=("Guarded",), cand_incomplete=("Guarded",))
        self.assertEqual(summary["mismatches"], ["base probe of Guarded did not run to completion",
                                                 "candidate probe of Guarded did not run to completion",
                                                 "abnormal exit 137 in base Guarded/exit",
                                                 "abnormal exit 137 in candidate Guarded/exit"])

    def test_missing_and_extra_dumps_fail(self) -> None:
        candidate = two_imports()
        del candidate["ModuleA"]["N.one.model"]
        candidate["ModuleB"]["N.three.model"] = model()
        summary = self.compare(two_imports(), candidate, cand_targets=None)
        self.assertIn("only in base: ModuleA/N.one.model", summary["mismatches"])
        self.assertIn("only in candidate: ModuleB/N.three.model", summary["mismatches"])

    def test_target_list_difference_fails(self) -> None:
        summary = self.compare(two_imports(), two_imports(), cand_targets={"ModuleA": ["N.one"]})
        self.assertIn("targets differ", summary["mismatches"])

    def test_unbuilt_dumps_are_not_evidence(self) -> None:
        summary = self.compare(two_imports(), two_imports(), cand_built=False)
        self.assertEqual(summary["mismatches"], ["candidate dump was not built before probing"])

    def test_same_clean_revision_is_not_a_comparison(self) -> None:
        summary = self.compare(two_imports(), two_imports(), base_revision="r", cand_revision="r")
        self.assertEqual(summary["mismatches"], ["base and candidate are the same clean revision"])
        summary = harness.compare(self.dir / "base", write_dump(self.dir / "dirty", two_imports(),
                                                                 revision="r", dirty=True))
        self.assertEqual(summary["mismatches"], [])

    def test_identical_missing_build_failures_are_not_evidence(self) -> None:
        line = "<out>/probes/ModuleB.lean:1:0: error: object file <root>/.lake/build/lib/lean/X.olean of module X does not exist\n"
        summary = self.compare(two_imports(), two_imports(), base_diagnostics={"ModuleB": line},
                               cand_diagnostics={"ModuleB": line})
        self.assertEqual(summary["mismatches"], ["missing build output in base ModuleB/diagnostics.txt",
                                                 "missing build output in candidate ModuleB/diagnostics.txt"])

    def test_targets_without_a_value_are_listed(self) -> None:
        targets = {"ModuleA": ["N.one", "N.two"], "ModuleB": ["N.three", "N.rejected"]}
        guarded = {"ModuleB": ["N.rejected"]}
        summary = self.compare(two_imports(), two_imports(), base_targets=targets, cand_targets=targets,
                               base_guarded=guarded, cand_guarded=guarded)
        self.assertEqual(summary["mismatches"], [])
        self.assertEqual(summary["targets_without_value"], ["ModuleB: N.rejected"])

    def test_unguarded_target_without_a_value_fails(self) -> None:
        targets = {"ModuleA": ["N.one", "N.two"], "ModuleB": ["N.three", "N.lost"]}
        summary = self.compare(two_imports(), two_imports(), base_targets=targets, cand_targets=targets)
        self.assertEqual(summary["mismatches"], ["no value for an import not pinned by #guard_msgs: ModuleB: N.lost"])

    def test_identical_errors_in_module_source_fail(self) -> None:
        lines = {"ModuleA": 40, "ModuleB": 40}
        error = "<out>/probes/ModuleB.lean:12:0: error: solc binary checksum mismatch\n"
        probe_error = "<out>/probes/ModuleB.lean:43:0: error: unknown identifier 'N.rejected.model'\n"
        summary = self.compare(two_imports(), two_imports(), base_source_lines=lines, cand_source_lines=lines,
                               base_diagnostics={"ModuleB": error + probe_error},
                               cand_diagnostics={"ModuleB": error + probe_error})
        self.assertEqual(summary["mismatches"], ["error in module source in base ModuleB/diagnostics.txt: line 12",
                                                 "error in module source in candidate ModuleB/diagnostics.txt: line 12"])

    def test_subset_dumps_need_explicit_consent(self) -> None:
        base = write_dump(self.dir / "b", two_imports(), subset=True)
        candidate = write_dump(self.dir / "c", two_imports(), subset=True)
        self.assertEqual(harness.compare(base, candidate)["mismatches"],
                         ["base dump covers only some modules (pass --allow-subset)",
                          "candidate dump covers only some modules (pass --allow-subset)"])
        self.assertEqual(harness.compare(base, candidate, allow_subset=True)["mismatches"], [])

    def test_dumps_without_models_are_not_evidence(self) -> None:
        only_reports = {"ModuleB": {"N.three.report": report(DIGEST_A)}}
        summary = self.compare(only_reports, only_reports)
        self.assertEqual(summary["mismatches"], ["no model compared: the dumps are not evidence"])

    def test_report_without_exactly_one_digest_is_a_harness_error(self) -> None:
        for text in ("{ contract := \"C\" }\n", report(DIGEST_A) + report(DIGEST_A)):
            with self.subTest(text=text[:20]):
                base = {"M": {"N.model": model(), "N.report": text}}
                with tempfile.TemporaryDirectory() as tmp:
                    with self.assertRaises(HarnessError):
                        harness.compare(write_dump(Path(tmp) / "b", base), write_dump(Path(tmp) / "c", base))

    def test_directory_without_manifest_is_rejected(self) -> None:
        (self.dir / "empty").mkdir()
        with self.assertRaises(HarnessError):
            harness.compare(self.dir / "empty", self.dir / "empty")

    def test_cli_exit_codes(self) -> None:
        base = write_dump(self.dir / "b", two_imports())
        same = write_dump(self.dir / "s", two_imports(DIGEST_B))
        other = write_dump(self.dir / "o", two_imports(second_model="z"))
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(harness.main(["compare", str(base), str(same)]), 0)
            self.assertEqual(harness.main(["compare", str(base), str(other)]), 1)
            self.assertEqual(harness.main(["compare", str(base), str(self.dir)]), 2)


class TargetTests(unittest.TestCase):
    def test_names_follow_namespaces_and_skip_comments_and_nested_text(self) -> None:
        source = """import Compiler.SolidityImport.Import
namespace Outer
solidity_import first from "d" entry "A.sol"
  contract C
-- solidity_import commented from "d"
/- solidity_import blockCommented
   /- nested -/ solidity_import stillCommented -/
section
#guard_msgs in
solidity_import guarded from "d" entry "A.sol"
end
namespace Inner.Deep
solidity_import deep from "d" entry "A.sol"
end Inner.Deep
  solidity_import indentedIsNotTopLevel
def s := "-- solidity_import inString"
end Outer
solidity_import top from "d"
#guard_msgs in solidity_import sameLine from "d"
"""
        self.assertEqual(harness.import_targets(source),
                         [("Outer.first", False), ("Outer.guarded", True), ("Outer.Inner.Deep.deep", False),
                          ("top", False), ("sameLine", True)])

    def test_scope_errors_are_reported(self) -> None:
        for source in ("end Foo\n", "namespace A\nend B\n",
                       "solidity_import x from \"d\"\nsolidity_import x from \"d\"\n"):
            with self.subTest(source=source):
                with self.assertRaises(HarnessError):
                    harness.import_names(source)

    def test_in_tree_smoke_targets(self) -> None:
        found = harness.targets(harness.ROOT)
        names = [name for module in found.values() for name in module]
        self.assertGreater(len(found), 50)
        self.assertGreater(len(names), 100)
        self.assertEqual(len(names), len(set(names)))
        self.assertTrue(all(found.values()))

    def test_module_imports_are_the_leading_import_lines(self) -> None:
        source = "/- header -/\nimport A.B\n-- note\nimport C\n\nopen A\nimport NotLeading\n"
        self.assertEqual(harness.module_imports(source), ["A.B", "C"])

    def test_unknown_module_is_rejected(self) -> None:
        with self.assertRaises(HarnessError):
            harness.targets(harness.ROOT, ["NoSuchSmokeModule"])

    def test_probe_appends_one_dump_per_value(self) -> None:
        text = harness.probe_text("import X\n\nsolidity_import a from \"d\"\n", ["N.a"], Path('/tmp/o "q"'))
        self.assertTrue(text.startswith("import X\n\nsolidity_import a"))
        self.assertIn('#eval IO.FS.writeFile "/tmp/o \\"q\\"/N.a.model" (toString (repr N.a.model) ++ "\\n")', text)
        self.assertIn('(toString (repr N.a.report) ++ "\\n")', text)
        self.assertEqual(text.count("#eval"), 3)
        self.assertTrue(text.endswith('#eval IO.FS.writeFile "/tmp/o \\"q\\"/complete" ""\n'))

    def test_probe_only_dump_of_in_tree_module(self) -> None:
        module = next(iter(harness.targets(harness.ROOT)))
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / harness.SMOKE).mkdir(parents=True)
            source = (harness.ROOT / harness.SMOKE / f"{module}.lean").read_text()
            (root / harness.SMOKE / f"{module}.lean").write_text(source)
            with self.assertRaises(HarnessError):
                harness.dump(root, Path(tmp + "-elsewhere"), [module], [], probe_only=True)
            out = root / ".lake" / "dump"
            manifest = harness.dump(root, out, [module], [], probe_only=True)
            self.assertTrue(manifest["subset"])
            self.assertEqual(manifest["source_lines"][module], len(source.rstrip("\n").splitlines()))
            probe = (out / "probes" / f"{module}.lean").read_text()
            self.assertEqual(list(manifest["targets"]), [module])
            self.assertEqual(probe.count("#eval IO.FS.writeFile"), 2 * len(manifest["targets"][module]) + 1)
            self.assertFalse(json.loads((out / "manifest.json").read_text())["built"])
            self.assertIn("Compiler.SolidityImport.Import", manifest["imports"])
            with self.assertRaises(HarnessError):
                harness.dump(harness.ROOT, out, [module], [], probe_only=True)

    def test_paths_are_normalized_longest_first(self) -> None:
        root = Path("/w/repo")
        out = Path("/w/repo/.lake/equiv")
        text = "/w/repo/.lake/equiv/probes/M.lean:1:0: x /w/repo/Compiler/A.lean"
        self.assertEqual(harness.normalize_paths(text, root, out), "<out>/probes/M.lean:1:0: x <root>/Compiler/A.lean")


class AnchorTests(unittest.TestCase):
    def test_in_tree_anchors_are_unique_or_known(self) -> None:
        anchors, problems = harness.collect_anchors()
        self.assertEqual(problems, [])
        self.assertEqual(harness.anchor_problems(anchors), [])
        importer = [a for a in anchors if a.file.startswith("Compiler/SolidityImport/")]
        self.assertGreater(len(importer), 300)
        self.assertTrue(any(a.file == harness.IMPORT for a in anchors))
        self.assertTrue(any(a.file != harness.IMPORT for a in importer))

    def test_every_mutant_table_is_classified(self) -> None:
        declared, problems = harness.declared_tables(SCRIPT_DIR / "solidity_differential")
        self.assertEqual(problems, [])
        self.assertEqual(set(declared), set(harness.MUTANT_TABLES) | set(harness.NOT_ANCHOR_TABLES))

    def test_unclassified_table_is_reported(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            package = Path(tmp)
            (package / "check_new_mutations.py").write_text("MUTANTS = {}\n")
            _, problems = harness.declared_tables(package)
        self.assertIn("check_new_mutations: MUTANTS table with no routing in check_importer_move_equivalence.py",
                      problems)

    def test_moved_duplicated_and_known_anchor_controls(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Old.lean").write_text("alpha\nbeta\nbeta\n")
            (root / "New.lean").write_text("gamma\n")
            anchors = [Anchor("s", "unique", "Old.lean", "alpha"),
                       Anchor("s", "duplicated", "Old.lean", "beta"),
                       Anchor("s", "moved-away", "Old.lean", "gamma"),
                       Anchor("s", "rerouted", "New.lean", "gamma"),
                       Anchor("s", "missing-file", "Gone.lean", "alpha"),
                       Anchor("s", "empty", "Old.lean", ""),
                       Anchor("s", "known-same", "Old.lean", "beta"),
                       Anchor("s", "known-changed", "Old.lean", "alpha"),
                       Anchor("s", "no-op", "New.lean", "gamma", "gamma"),
                       Anchor("s", "mutates", "New.lean", "gamma", "delta")]
            known = {("s", "known-same"): 2, ("s", "known-changed"): 0, ("s", "retired"): 0}
            problems = harness.anchor_problems(anchors, root, known)
        self.assertEqual(problems, [
            "s: duplicated: anchor occurs 2 times in Old.lean",
            "s: moved-away: anchor occurs 0 times in Old.lean",
            "s: missing-file: anchor occurs 0 times in Gone.lean",
            "s: empty: anchor occurs 0 times in Old.lean",
            "s: known-changed: known anchor problem changed (0 -> 1 in Old.lean); update KNOWN_ANCHOR_PROBLEMS",
            "s: no-op: replacement equals the anchor",
            "s: retired: listed in KNOWN_ANCHOR_PROBLEMS but no longer a mutant",
        ])

    def test_inline_anchor_extraction(self) -> None:
        source = ("def f():\n    anchor = 'a\\nb'\n"
                  "def g():\n    rules = [('one', 'x', 'y'), ('two', 'z', 'w')]\n")
        self.assertEqual(harness.inline_anchors("s", source), [
            Anchor("s", "s", harness.IMPORT, "a\nb"),
            Anchor("s", "one", harness.IMPORT, "x"),
            Anchor("s", "two", harness.IMPORT, "z")])


if __name__ == "__main__":
    unittest.main()
