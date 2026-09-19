#!/usr/bin/env python3
"""Install the official pinned solc for the Lean Solidity importer.

Fetches binaries.soliditylang.org `<platform>/list.json`, checks that the
published 0.8.33 SHA-256 still matches the committed pin, then downloads that
build to `.lake/solidity-import/solc`. Lake never performs this fetch.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import sys
import urllib.request
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import official_solc

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DEST = ROOT / ".lake" / "solidity-import" / "solc"


def host_platform() -> str:
    if sys.platform == "darwin":
        return "macosx-amd64"
    if sys.platform.startswith("linux") and platform.machine() in ("x86_64", "amd64"):
        return "linux-amd64"
    raise RuntimeError(
        f"no official solc pin for {sys.platform} {platform.machine()}"
    )


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def install(dest: Path, platform_name: str) -> None:
    expected = official_solc.OFFICIAL_SOLC_SHA256[platform_name]
    published = official_solc.published_build(official_solc.fetch_list(platform_name))
    if published["sha256"] != expected:
        raise RuntimeError(
            f"{platform_name} list.json SHA-256 {published['sha256']} "
            f"does not match committed pin {expected}"
        )
    dest.parent.mkdir(parents=True, exist_ok=True)
    url = official_solc.binary_url(platform_name, published["path"])
    tmp = dest.with_name(dest.name + ".tmp")
    try:
        request = urllib.request.Request(
            url,
            headers={"User-Agent": "verity-official-solc/0.8.33"},
        )
        with urllib.request.urlopen(request, timeout=60) as response, tmp.open("wb") as handle:
            handle.write(response.read())
        got = file_sha256(tmp)
        if got != expected:
            raise RuntimeError(f"downloaded {url} SHA-256 {got} != {expected}")
        tmp.replace(dest)
        dest.chmod(0o755)
    finally:
        if tmp.exists():
            tmp.unlink()
    print(f"installed official solc {official_solc.SOLC_LONG_VERSION} ({platform_name}) at {dest}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dest",
        type=Path,
        default=DEFAULT_DEST,
        help="destination path (default: .lake/solidity-import/solc)",
    )
    parser.add_argument(
        "--platform",
        choices=sorted(official_solc.OFFICIAL_SOLC_SHA256),
        help="override host platform (default: detect)",
    )
    args = parser.parse_args()
    try:
        install(args.dest, args.platform or host_platform())
    except (RuntimeError, ValueError, OSError) as err:
        print(f"solc importer setup failed: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
