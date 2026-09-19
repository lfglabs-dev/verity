"""Official Solidity binary pins from binaries.soliditylang.org.

`solc-select` reads `<platform>/list.json` and downloads the matching `path`.
This module stores the published SHA-256 digests for the pinned release and
parses/fetches those lists. Lake elaboration never fetches; only setup and the
optional pin-check flag talk to the network.
"""

from __future__ import annotations

import json
import urllib.error
import urllib.request
from typing import Any

SOLC_VERSION = "0.8.33"
SOLC_COMMIT = "64118f21"
SOLC_LONG_VERSION = f"{SOLC_VERSION}+commit.{SOLC_COMMIT}"

# builds[].sha256 from list.json, without the leading 0x.
OFFICIAL_SOLC_SHA256 = {
    "linux-amd64": "1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468",
    "macosx-amd64": "8324280591ce398d7e2722846bc10ecf1779b13a328ef97b687c92cd9c70801a",
}

LIST_URL = "https://binaries.soliditylang.org/{platform}/list.json"
BINARY_URL = "https://binaries.soliditylang.org/{platform}/{path}"


def normalize_sha256(value: str) -> str:
    text = value.strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != 64 or any(c not in "0123456789abcdef" for c in text):
        raise ValueError(f"invalid SHA-256 digest: {value!r}")
    return text


def published_build(list_payload: dict[str, Any], long_version: str = SOLC_LONG_VERSION) -> dict[str, str]:
    """Return `{path, sha256}` for `long_version` from a list.json object."""
    builds = list_payload.get("builds")
    if not isinstance(builds, list):
        raise ValueError("list.json: missing builds array")
    for entry in builds:
        if not isinstance(entry, dict):
            continue
        if entry.get("longVersion") != long_version:
            continue
        path = entry.get("path")
        sha256 = entry.get("sha256")
        if not isinstance(path, str) or not isinstance(sha256, str):
            raise ValueError(f"list.json: incomplete build for {long_version}")
        return {"path": path, "sha256": normalize_sha256(sha256)}
    raise ValueError(f"list.json: no build for {long_version}")


def list_url(platform: str) -> str:
    if platform not in OFFICIAL_SOLC_SHA256:
        raise ValueError(f"unsupported official solc platform: {platform}")
    return LIST_URL.format(platform=platform)


def binary_url(platform: str, path: str) -> str:
    if "/" in path or path.startswith("."):
        raise ValueError(f"refusing non-canonical solc path: {path!r}")
    return BINARY_URL.format(platform=platform, path=path)


def fetch_list(platform: str, timeout: float = 20.0) -> dict[str, Any]:
    url = list_url(platform)
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "verity-official-solc/0.8.33"},
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.loads(response.read().decode("utf-8"))
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, OSError) as err:
        raise RuntimeError(f"failed to fetch {url}: {err}") from err
    if not isinstance(payload, dict):
        raise RuntimeError(f"{url}: expected a JSON object")
    return payload


def published_sha256(platform: str, long_version: str = SOLC_LONG_VERSION) -> str:
    return published_build(fetch_list(platform), long_version)["sha256"]
