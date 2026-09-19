#!/usr/bin/env python3
"""Enforce pinned solc version consistency across CI, tooling, and docs.

Issue #76 depends on stable Yul->bytecode semantics. This script prevents
silent compiler-version drift by requiring one canonical solc version across:
  - GitHub Actions verify workflow env vars
  - foundry.toml profile config
  - trust assumptions documentation
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import official_solc

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
SETUP_SOLC_ACTION = ROOT / ".github" / "actions" / "setup-solc" / "action.yml"
FOUNDRY_TOML = ROOT / "foundry.toml"
TRUST_ASSUMPTIONS = ROOT / "TRUST_ASSUMPTIONS.md"
MACOS_SOLC_SHA256 = official_solc.OFFICIAL_SOLC_SHA256["macosx-amd64"]

SOLC_VERSION_RE = re.compile(r'^\s*SOLC_VERSION:\s*"([^"]+)"\s*$', re.MULTILINE)
SOLC_URL_RE = re.compile(r'^\s*SOLC_URL:\s*"([^"]+)"\s*$', re.MULTILINE)
SOLC_SHA256_RE = re.compile(r'^\s*SOLC_SHA256:\s*"([0-9a-fA-F]{64})"\s*$', re.MULTILINE)

URL_VERSION_RE = re.compile(r"solc-linux-amd64-v(\d+\.\d+\.\d+)\+commit\.([0-9a-fA-F]{8})$")
FOUNDRY_SOLC_RE = re.compile(r'^\s*solc_version\s*=\s*"([^"]+)"\s*$', re.MULTILINE)
TRUST_PIN_RE = re.compile(r"\*\*Version\*\*:\s*([0-9]+\.[0-9]+\.[0-9]+\+commit\.[0-9a-fA-F]{8})\s+\(pinned\)")
SOLC_DOWNLOAD_RE = re.compile(r"curl\b[^\n]*\s\"\$SOLC_URL\"\s+-o\s+solc")


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"missing file: {path.relative_to(ROOT)}")
    return path.read_text(encoding="utf-8")


def _collect(pattern: re.Pattern[str], text: str, label: str) -> list[str]:
    values = [m.group(1) for m in pattern.finditer(text)]
    if not values:
        raise ValueError(f"could not parse {label}")
    return values


def _extract_canonical(
    pattern: re.Pattern[str], text: str, label: str, errors: list[str]
) -> str:
    values = _collect(pattern, text, label)
    canonical = values[0]
    for idx, value in enumerate(values[1:], start=2):
        if value != canonical:
            errors.append(
                f".github/workflows/verify.yml: {label} occurrence {idx} "
                f"('{value}') conflicts with canonical '{canonical}'"
            )
    return canonical


def _verify_published_checksums(errors: list[str]) -> None:
    for platform_name, expected in official_solc.OFFICIAL_SOLC_SHA256.items():
        try:
            published = official_solc.published_sha256(platform_name)
        except RuntimeError as err:
            errors.append(str(err))
            continue
        if published != expected:
            errors.append(
                f"binaries.soliditylang.org {platform_name} {official_solc.SOLC_LONG_VERSION} "
                f"SHA-256 {published} does not match committed pin {expected}"
            )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--verify-published-checksums",
        action="store_true",
        help="fetch official list.json files and require SHA-256 pins to match",
    )
    args = parser.parse_args([] if argv is None else argv)
    errors: list[str] = []

    try:
        verify_text = _read(VERIFY_YML)
        action_text = _read(SETUP_SOLC_ACTION)
        foundry_text = _read(FOUNDRY_TOML)
        trust_text = _read(TRUST_ASSUMPTIONS)
    except (FileNotFoundError, OSError) as err:
        print(f"solc pin check failed: {err}", file=sys.stderr)
        return 1

    try:
        solc_version = _extract_canonical(SOLC_VERSION_RE, verify_text, "SOLC_VERSION", errors)
        solc_url = _extract_canonical(SOLC_URL_RE, verify_text, "SOLC_URL", errors)
        linux_sha256 = _extract_canonical(SOLC_SHA256_RE, verify_text, "SOLC_SHA256", errors)
    except ValueError as err:
        print(f"solc pin check failed: {err}", file=sys.stderr)
        return 1

    url_match = URL_VERSION_RE.search(solc_url)
    if url_match is None:
        errors.append(
            ".github/workflows/verify.yml: SOLC_URL does not match expected solidity binary form"
        )
        url_version = None
        url_commit = None
    else:
        url_version, url_commit = url_match.group(1), url_match.group(2)
        if url_version != solc_version:
            errors.append(
                ".github/workflows/verify.yml: SOLC_VERSION does not match SOLC_URL embedded version"
            )

    foundry_solc = FOUNDRY_SOLC_RE.search(foundry_text)
    if foundry_solc is None:
        errors.append("foundry.toml: missing solc_version")
    elif foundry_solc.group(1) != solc_version:
        errors.append("foundry.toml: solc_version must match verify.yml SOLC_VERSION")

    trust_pin = TRUST_PIN_RE.search(trust_text)
    if trust_pin is None:
        errors.append(
            "TRUST_ASSUMPTIONS.md: missing pinned solc version line ('**Version**: <semver+commit> (pinned)')"
        )
    elif url_commit is not None and trust_pin.group(1) != f"{solc_version}+commit.{url_commit}":
        errors.append(
            "TRUST_ASSUMPTIONS.md: pinned solc version must match verify.yml SOLC_VERSION/SOLC_URL"
        )

    if SOLC_DOWNLOAD_RE.search(action_text) is None:
        errors.append(".github/actions/setup-solc/action.yml: install step must download from $SOLC_URL")
    if 'echo "${SOLC_SHA256}  solc" | sha256sum -c -' not in action_text:
        errors.append(".github/actions/setup-solc/action.yml: install step must verify $SOLC_SHA256")
    if "/usr/local/bin/solc" in action_text:
        errors.append(".github/actions/setup-solc/action.yml: solc cache/install path must be workspace-local")
    if re.search(r"\bsudo\b", action_text):
        errors.append(".github/actions/setup-solc/action.yml: solc install step must not require sudo")

    importer = ROOT / "Contracts" / "VaultFromSolidity" / "Importer" / "Importer.lean"
    if linux_sha256 != official_solc.OFFICIAL_SOLC_SHA256["linux-amd64"]:
        errors.append(
            ".github/workflows/verify.yml: SOLC_SHA256 must be the official "
            "linux-amd64 list.json digest"
        )

    if importer.exists():
        importer_text = _read(importer)
        if official_solc.SOLC_LONG_VERSION not in importer_text:
            errors.append(
                "Contracts/VaultFromSolidity/Importer/Importer.lean: "
                f"must pin solcVersionPin {official_solc.SOLC_LONG_VERSION}"
            )
        if linux_sha256 not in importer_text:
            errors.append(
                "Contracts/VaultFromSolidity/Importer/Importer.lean: "
                "must pin verify.yml SOLC_SHA256 for linux-amd64"
            )
        if MACOS_SOLC_SHA256 not in importer_text:
            errors.append(
                "Contracts/VaultFromSolidity/Importer/Importer.lean: "
                "must pin the official macosx-amd64 solc SHA-256"
            )
        if "officialSolcSha256s" not in importer_text:
            errors.append(
                "Contracts/VaultFromSolidity/Importer/Importer.lean: "
                "must accept official solc builds via officialSolcSha256s"
            )
        if "/usr/bin/shasum" not in importer_text:
            errors.append(
                "Contracts/VaultFromSolidity/Importer/Importer.lean: "
                "macOS checksum path must be /usr/bin/shasum"
            )

    if args.verify_published_checksums:
        _verify_published_checksums(errors)

    if errors:
        print("solc pin check failed:", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        return 1

    print(
        "✓ solc pin is consistent "
        f"({solc_version}{'' if url_commit is None else f'+commit.{url_commit}'})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
