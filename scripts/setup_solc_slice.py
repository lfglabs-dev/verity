#!/usr/bin/env python3
"""Install pinned solc 0.8.34 for the function-slice importer.

The Vault importer keeps solc 0.8.33 at `.lake/solidity-import/solc`.
This script writes `.lake/solidity-import/solc-0.8.34` and does not replace it.
Lake elaboration never downloads the compiler.
"""

from __future__ import annotations

import hashlib
import platform
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / ".lake" / "solidity-import" / "solc-0.8.34"
LONG_VERSION = "0.8.34+commit.80d5c536"
SHA256 = {
    "linux-amd64": "d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39",
    "macosx-amd64": "0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746",
}


def host_platform() -> str:
    if sys.platform == "darwin":
        return "macosx-amd64"
    if sys.platform.startswith("linux") and platform.machine() in ("x86_64", "amd64"):
        return "linux-amd64"
    raise RuntimeError(f"no solc 0.8.34 pin for {sys.platform} {platform.machine()}")


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def install(platform_name: str) -> None:
    expected = SHA256[platform_name]
    list_url = f"https://binaries.soliditylang.org/{platform_name}/list.json"
    request = urllib.request.Request(list_url, headers={"User-Agent": "verity-official-solc/0.8.34"})
    import json
    with urllib.request.urlopen(request, timeout=60) as response:
        payload = json.load(response)
    match = None
    for entry in payload.get("builds", []):
        if entry.get("longVersion") == LONG_VERSION:
            match = entry
            break
    if match is None:
        raise RuntimeError(f"list.json has no build for {LONG_VERSION}")
    published = str(match["sha256"])
    if published.startswith("0x"):
        published = published[2:]
    if published != expected:
        raise RuntimeError(f"list.json SHA-256 {published} != pin {expected}")
    url = f"https://binaries.soliditylang.org/{platform_name}/{match['path']}"
    DEST.parent.mkdir(parents=True, exist_ok=True)
    tmp = DEST.with_name(DEST.name + ".tmp")
    try:
        binary = urllib.request.Request(url, headers={"User-Agent": "verity-official-solc/0.8.34"})
        with urllib.request.urlopen(binary, timeout=60) as response, tmp.open("wb") as handle:
            handle.write(response.read())
        got = file_sha256(tmp)
        if got != expected:
            raise RuntimeError(f"downloaded SHA-256 {got} != {expected}")
        tmp.replace(DEST)
        DEST.chmod(0o755)
    finally:
        if tmp.exists():
            tmp.unlink()
    print(f"installed {LONG_VERSION} ({platform_name}) at {DEST}")


def main() -> int:
    if DEST.exists() and file_sha256(DEST) == SHA256[host_platform()]:
        print(f"already installed at {DEST}")
        return 0
    install(host_platform())
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
