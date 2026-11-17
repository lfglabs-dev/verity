#!/usr/bin/env python3
"""Print the current repository counts (tests, theorems, coverage, lines, proofs).

The counts are computed from source files (`verification_metrics.current_metrics()`,
about 20 s, no Lean build); no committed file holds them. Default output is one
`dotted.key: value` line per metric; `--json` prints the full JSON object.
Run as `make status` (`make status ARGS=--json`).
"""

from __future__ import annotations

import argparse
from typing import Any

from verification_metrics import current_metrics, render_metrics_json


def flatten(data: dict[str, Any], prefix: str = "") -> list[tuple[str, Any]]:
    """Return (dotted.key, value) pairs in insertion order."""
    pairs: list[tuple[str, Any]] = []
    for key, value in data.items():
        dotted = f"{prefix}{key}"
        if isinstance(value, dict):
            pairs.extend(flatten(value, f"{dotted}."))
        else:
            pairs.append((dotted, value))
    return pairs


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="Print the metrics as JSON.")
    args = parser.parse_args(argv)
    metrics = current_metrics()
    if args.json:
        print(render_metrics_json(metrics), end="")
        return
    for key, value in flatten(metrics):
        print(f"{key}: {value}")


if __name__ == "__main__":
    main()
