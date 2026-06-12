"""Tests for property_pipeline.py (P7 Cluster C consolidation)."""

from __future__ import annotations

import unittest

import property_pipeline


class TestPropertyPipelineCli(unittest.TestCase):
    def test_check_rejects_unknown_only(self) -> None:
        with self.assertRaises(SystemExit) as ctx:
            property_pipeline.main(["check", "--only", "nonsense"])
        self.assertEqual(ctx.exception.code, 2)

    def test_requires_subcommand(self) -> None:
        with self.assertRaises(SystemExit) as ctx:
            property_pipeline.main([])
        self.assertEqual(ctx.exception.code, 2)

    def test_check_order_is_stable(self) -> None:
        self.assertEqual(property_pipeline.CHECKS, ("manifest", "coverage", "lean-sync"))


class TestShimsDelegate(unittest.TestCase):
    def test_legacy_shims_import_pipeline(self) -> None:
        import check_property_coverage
        import check_property_manifest
        import check_property_manifest_sync
        import extract_property_manifest
        import report_property_coverage

        for shim in (
            check_property_manifest,
            check_property_coverage,
            check_property_manifest_sync,
            extract_property_manifest,
            report_property_coverage,
        ):
            self.assertIs(shim.pipeline_main, property_pipeline.main)


if __name__ == "__main__":
    unittest.main()
