#!/usr/bin/env python3
"""Write the repository verification metrics to a JSON file, on demand.

The output (default `artifacts/verification_status.json`) is a git-ignored
cache for tools that prefer a file; checks compute the metrics in memory with
`verification_metrics.current_metrics()`, so nothing committed holds them.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from property_utils import ROOT
from verification_metrics import current_metrics


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Write the current verification metrics as JSON (a build output, not committed)."
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "artifacts" / "verification_status.json",
        help="Output JSON path.",
    )
    args = parser.parse_args()

    current_metrics(cache=args.output)
    print(f"Wrote verification metrics: {args.output}")


if __name__ == "__main__":
    main()
