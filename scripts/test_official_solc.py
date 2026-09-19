#!/usr/bin/env python3
from __future__ import annotations

import unittest

import official_solc


class OfficialSolcTests(unittest.TestCase):
    def test_normalize_sha256_strips_prefix(self) -> None:
        digest = "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468"
        self.assertEqual(official_solc.normalize_sha256("0x" + digest), digest)
        self.assertEqual(official_solc.normalize_sha256(digest.upper()), digest)

    def test_published_build_reads_long_version(self) -> None:
        payload = {
            "builds": [
                {
                    "path": "solc-linux-amd64-v0.8.32+commit.deadbeef",
                    "longVersion": "0.8.32+commit.deadbeef",
                    "sha256": "0x" + ("ab" * 32),
                },
                {
                    "path": "solc-linux-amd64-v0.8.33+commit.64118f21",
                    "longVersion": official_solc.SOLC_LONG_VERSION,
                    "sha256": "0x" + official_solc.OFFICIAL_SOLC_SHA256["linux-amd64"],
                },
            ]
        }
        build = official_solc.published_build(payload)
        self.assertEqual(build["path"], "solc-linux-amd64-v0.8.33+commit.64118f21")
        self.assertEqual(build["sha256"], official_solc.OFFICIAL_SOLC_SHA256["linux-amd64"])

    def test_published_build_rejects_missing_release(self) -> None:
        with self.assertRaises(ValueError):
            official_solc.published_build({"builds": []})

    def test_binary_url_rejects_path_escape(self) -> None:
        with self.assertRaises(ValueError):
            official_solc.binary_url("linux-amd64", "../solc")


if __name__ == "__main__":
    unittest.main()
