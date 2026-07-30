#!/usr/bin/env python3
"""Run macro-health CI checks behind one entrypoint."""

from __future__ import annotations

import argparse

import check_macro_property_test_generation
import check_macro_roundtrip_fuzz_coverage


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse command-line arguments for macro-health checks.

    Args:
        argv: List of command-line arguments. Defaults to None, which
            uses sys.argv[1:].

    Returns:
        argparse.Namespace object containing parsed arguments.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-property-tests", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)

    if not args.skip_property_tests:
        rc = check_macro_property_test_generation.main(["--check"])
        if rc != 0:
            return rc

    rc = check_macro_roundtrip_fuzz_coverage.main([])
    if rc != 0:
        return rc

    print("macro health checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
