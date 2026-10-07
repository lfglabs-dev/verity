#!/usr/bin/env python3
"""Install pinned solc 0.8.34 or 0.8.10 for the Solidity importer (`solidity_import`).

The binaries are written to `.lake/solidity-import/solc-0.8.34` and
`.lake/solidity-import/solc-0.8.10`. Lake elaboration never downloads the compiler.
"""

from __future__ import annotations

import argparse
import hashlib
import platform
import shutil
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RELEASES = {
    "0.8.34": {
        "binary_name": "solc-0.8.34",
        "long_version": "0.8.34+commit.80d5c536",
        "sha256": {
            "linux-amd64": "d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39",
            "macosx-amd64": "0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746",
        },
    },
    "0.8.10": {
        "binary_name": "solc-0.8.10",
        "long_version": "0.8.10+commit.fc410830",
        "sha256": {
            "linux-amd64": "c7effacf28b9d64495f81b75228fbf4266ac0ec87e8f1adc489ddd8a4dd06d89",
            "macosx-amd64": "a79fff23aeb35be856e446827c44a9cfa4c382f29babd2f6a405ef73d1e2a4cc",
        },
    },
}


def host_platform() -> str:
    if sys.platform == "darwin":
        return "macosx-amd64"
    if sys.platform.startswith("linux") and platform.machine() in ("x86_64", "amd64"):
        return "linux-amd64"
    raise RuntimeError(f"no solc pin for {sys.platform} {platform.machine()}")


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def install(version: str, platform_name: str, dest: Path) -> None:
    release = RELEASES[version]
    long_version = release["long_version"]
    expected = release["sha256"][platform_name]
    cached = ROOT / ".lake" / "coverage" / "compilers" / release["binary_name"]
    if cached.exists() and file_sha256(cached) == expected:
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(cached, dest)
        dest.chmod(0o755)
        print(f"installed {long_version} ({platform_name}) at {dest} from local cache")
        return
    list_url = f"https://binaries.soliditylang.org/{platform_name}/list.json"
    request = urllib.request.Request(list_url, headers={"User-Agent": f"verity-official-solc/{version}"})
    import json
    with urllib.request.urlopen(request, timeout=60) as response:
        payload = json.load(response)
    match = None
    for entry in payload.get("builds", []):
        if entry.get("longVersion") == long_version:
            match = entry
            break
    if match is None:
        raise RuntimeError(f"list.json has no build for {long_version}")
    published = str(match["sha256"])
    if published.startswith("0x"):
        published = published[2:]
    if published != expected:
        raise RuntimeError(f"list.json SHA-256 {published} != pin {expected}")
    url = f"https://binaries.soliditylang.org/{platform_name}/{match['path']}"
    dest.parent.mkdir(parents=True, exist_ok=True)
    tmp = dest.with_name(dest.name + ".tmp")
    try:
        binary = urllib.request.Request(url, headers={"User-Agent": f"verity-official-solc/{version}"})
        with urllib.request.urlopen(binary, timeout=60) as response, tmp.open("wb") as handle:
            handle.write(response.read())
        got = file_sha256(tmp)
        if got != expected:
            raise RuntimeError(f"downloaded SHA-256 {got} != {expected}")
        tmp.replace(dest)
        dest.chmod(0o755)
    finally:
        if tmp.exists():
            tmp.unlink()
    print(f"installed {long_version} ({platform_name}) at {dest}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", choices=tuple(RELEASES), default="0.8.34", help="pinned solc release")
    parser.add_argument("--all", action="store_true", help="install all pinned solc releases into .lake/solidity-import/")
    parser.add_argument("--output", type=Path, help="destination binary path")
    args = parser.parse_args()
    platform_name = host_platform()
    if args.all:
        if args.output is not None:
            raise RuntimeError("--output cannot be combined with --all")
        for version, release in RELEASES.items():
            dest = ROOT / ".lake" / "solidity-import" / release["binary_name"]
            if dest.exists() and file_sha256(dest) == release["sha256"][platform_name]:
                print(f"already installed at {dest}")
            else:
                install(version, platform_name, dest)
        return 0
    release = RELEASES[args.version]
    dest = args.output or (ROOT / ".lake" / "solidity-import" / release["binary_name"])
    if dest.exists() and file_sha256(dest) == release["sha256"][platform_name]:
        print(f"already installed at {dest}")
        return 0
    install(args.version, platform_name, dest)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
