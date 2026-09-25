#!/usr/bin/env python3
"""Capture actual optimized solc IR; this does not certify equivalence."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent
MIDNIGHT = "96d31343e993329e7a593dde46516a2c0cbcd142"
SOURCE = "src/libraries/UtilsLib.sol"
BLOB = "da30b5f2ae048eabdab031d6b4fac9caee442e0b"
SOLC = "0.8.34+commit.80d5c536"
HASHES = {
    "d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39",
    "0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746",
}
WRAPPER = """// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;
import {UtilsLib} from "src/libraries/UtilsLib.sol";
contract MulDivDown {
    function mulDivDown(uint256 x, uint256 y, uint256 d) external pure returns (uint256) {
        return UtilsLib.mulDivDown(x, y, d);
    }
}
"""


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--midnight-repo", type=Path, required=True)
    parser.add_argument("--solc", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    solc = args.solc.resolve()
    digest = sha(solc.read_bytes())
    if digest not in HASHES:
        raise SystemExit("unrecognized solc binary SHA-256: " + digest)
    version = subprocess.check_output([str(solc), "--version"], text=True).strip()
    if version not in {
        "solc, the solidity compiler commandline interface\nVersion: " + SOLC + suffix
        for suffix in (".Linux.g++", ".Darwin.appleclang")
    }:
        raise SystemExit("unexpected solc version: " + version)
    source = subprocess.check_output([
        "git", "-C", str(args.midnight_repo), "show", MIDNIGHT + ":" + SOURCE
    ])
    blob = hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
    if blob != BLOB:
        raise SystemExit("unexpected pinned UtilsLib git blob: " + blob)
    request = {
        "language": "Solidity",
        "sources": {
            SOURCE: {"content": source.decode()},
            "MulDivDown.sol": {"content": WRAPPER},
        },
        "settings": {
            "viaIR": True,
            "evmVersion": "osaka",
            "optimizer": {"enabled": True, "runs": 466},
            "metadata": {"bytecodeHash": "none"},
            "outputSelection": {"*": {"*": ["irOptimized", "irOptimizedAst", "evm.bytecode.object"]}},
        },
    }
    request_bytes = (json.dumps(request, indent=2, sort_keys=True) + "\n").encode()
    process = subprocess.run([str(solc), "--standard-json"], input=request_bytes,
                             capture_output=True, check=True)
    output = json.loads(process.stdout)
    errors = [e for e in output.get("errors", []) if e.get("severity") == "error"]
    if errors:
        raise SystemExit(json.dumps(errors, indent=2))
    contract = output["contracts"]["MulDivDown.sol"]["MulDivDown"]
    files = {
        "input.json": request_bytes,
        "MulDivDown.optimized.yul": contract["irOptimized"].encode(),
        "MulDivDown.optimized-ast.json": (json.dumps(contract["irOptimizedAst"], indent=2, sort_keys=True) + "\n").encode(),
    }
    # Materialize exactly the already-captured sources for solidity_import.
    files.update({"sources/" + name: item["content"].encode()
                  for name, item in request["sources"].items()})
    manifest = {
        "status": "compiler-output-capture-only; no equivalence theorem",
        "midnight_commit": MIDNIGHT,
        "source_path": SOURCE,
        "source_git_blob": BLOB,
        "source_sha256": sha(source),
        "solc": SOLC,
        "accepted_solc_sha256": sorted(HASHES),
        "evmyul_revision": "f7e4ee0dc8f8d5265ce822a937ab5be771f182e9",
        "artifacts_sha256": {name: sha(data) for name, data in files.items()},
    }
    files["manifest.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    for name, data in files.items():
        path = ROOT / name
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                raise SystemExit("capture differs: " + str(path))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
    print(("verified" if args.check else "captured") + " pinned optimized Yul and AST; no proof claimed")


if __name__ == "__main__":
    main()
