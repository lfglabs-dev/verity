"""Protocol, determinism and failure classification tests (stdlib only)."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential.cases import generate, canonical
from solidity_differential.engine import HarnessError, parse_evm, execute
from solidity_differential.programs import generated_campaign, source, smaller_expressions
from solidity_differential.reduce import reduce_failure, signature


class SolidityDifferentialTests(unittest.TestCase):
    def test_seed_reproduces_every_input(self):
        config = {"variables": {"a": 8, "b": 16}, "ordered_pairs": []}
        first = generate(config, 100, 17, [])
        self.assertEqual(first, generate(config, 100, 17, []))
        self.assertNotEqual(first, generate(config, 100, 18, []))
        self.assertTrue(all(0 <= v["a"] < 256 and 0 <= v["b"] < 65536 for _, v in first))
        self.assertEqual(len({name for name, _ in first}), 100)

    def test_corpus_and_defaults_are_preserved(self):
        result = generate({"variables": {"id": 256, "x": 8}, "defaults": {"id": 7}}, 0, 0, [{"name": "A", "x": "3"}])
        self.assertEqual(result, [("A", {"id": 7, "x": 3})])

    def test_nested_abi_signature(self):
        self.assertEqual(canonical({"type": "tuple[]", "components": [{"type": "uint256"}, {"type": "address"}]}), "(uint256,address)[]")

    def test_missing_bad_or_truncated_results_are_errors(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "results"
            for text in ("", "0 timeout 0x\n", "1 revert 0x\n", "0 ok 0x01\n", "0 revert 0x 1\n"):
                path.write_text(text)
                with self.assertRaises(HarnessError):
                    parse_evm(path, [{"id": "A", "observe": []}])
            path.write_text("0 revert 0x\n")
            self.assertEqual(parse_evm(path, [{"id": "A", "observe": []}])[0]["status"], "revert")

    def test_empty_or_stale_campaign_cannot_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "manifest.json").write_text(json.dumps({"implementationHashes": {}}))
            with patch("solidity_differential.engine.implementation_hashes", return_value={"changed": "x"}):
                with self.assertRaisesRegex(HarnessError, "implementation changed"):
                    execute(path, [])
            with patch("solidity_differential.engine.implementation_hashes", return_value={}):
                with self.assertRaisesRegex(HarnessError, "empty campaign"):
                    execute(path, [])

    def test_modified_bytecode_is_rejected_before_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / "source.bin").write_bytes(b"changed")
            (path / "manifest.json").write_text(json.dumps({
                "implementationHashes": {}, "artifactHashes": {"source.bin": "original"}}))
            with patch("solidity_differential.engine.implementation_hashes", return_value={}):
                with self.assertRaisesRegex(HarnessError, "campaign artifact changed"):
                    execute(path, [{"id": "A"}])

    def test_program_reduction_preserves_typed_tree(self):
        tree = {"kind": "binary", "op": "*", "left": {"kind": "x"}, "right": {"kind": "y"}}
        self.assertIn({"kind": "x"}, list(smaller_expressions(tree)))
        rendered = source({"bits": 248, "expression": tree, "helper": True, "renamed": False, "projection_collision": True})
        self.assertIn("uint248(x)", rendered)
        self.assertIn("_verity_slice.tmp_0", rendered)
        self.assertIn("L.work", rendered)

    def test_reducer_distinguishes_status_and_return_mismatches(self):
        a = {"status": "ok", "words": ["1"], "storage": [], "data": "0x01"}
        wrong_return = {**a, "words": ["2"]}
        reverted = {**a, "status": "revert", "words": []}
        self.assertNotEqual(signature({"source": a, "model": wrong_return, "compiled": a}),
                            signature({"source": a, "model": reverted, "compiled": a}))

    def test_metamorphic_divergence_is_recorded_and_not_reduced(self):
        def fake_campaign(fixture, run, cases, seed):
            out = Path(run) / "out"
            out.mkdir(parents=True, exist_ok=True)
            rows = "0 ok 0x01\n" if "program-0-0" in str(run) else "0 revert 0x\n"
            (out / "source.txt").write_text(rows)
            return {"cases": 1, "divergences": []}

        with tempfile.TemporaryDirectory() as directory:
            with patch("solidity_differential.programs.campaign", fake_campaign):
                report = generated_campaign(directory, 1, 0, 0)
            evidence = json.loads((Path(directory) / "metamorphic-divergence.json").read_text())
            self.assertEqual(report["divergences"], [evidence])
            self.assertEqual(evidence["rows"], [{"line": 0, "reference": "0 ok 0x01", "variant": "0 revert 0x"}])
            (Path(directory) / "results.json").write_text(json.dumps(report))
            with self.assertRaisesRegex(ValueError, "metamorphic"):
                reduce_failure(directory)


if __name__ == "__main__":
    unittest.main()
