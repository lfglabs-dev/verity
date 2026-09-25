#!/usr/bin/env python3
"""Run reproducible A/B/C comparisons for a declarative Solidity slice fixture."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
from solidity_differential.engine import HarnessError, campaign, execute


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--seed", type=int, default=2438)
    parser.add_argument("--cases", type=int, default=128, help="generated cases in addition to the fixed corpus")
    parser.add_argument("--replay", action="store_true", help="replay materialized cases in --output")
    parser.add_argument("--programs", type=int, default=0, help="generate this many source programs, each with a renamed/helper variant")
    parser.add_argument("--reduce", action="store_true", help="reduce the first recorded divergence")
    parser.add_argument("--reduce-seconds", type=int, default=120)
    parser.add_argument("--mutations", action="store_true", help="test importer and Denote mutants in isolated snapshots")
    parser.add_argument("--mutant", action="append", help="select a named mutant")
    parser.add_argument("--stateful", action="store_true", help="run stateful scalar A/B/C instrument checks")
    args = parser.parse_args()
    if args.cases < 0 or args.programs < 0 or args.reduce_seconds <= 0:
        parser.error("case/program counts must be nonnegative and reduction budget positive")
    if sum(map(bool, (args.config, args.replay, args.programs, args.reduce, args.mutations, args.stateful))) != 1:
        parser.error("choose exactly one of --config, --replay, --programs, --reduce, --mutations, --stateful")
    if args.mutant and not args.mutations:
        parser.error("--mutant requires --mutations")
    try:
        if args.stateful:
            from solidity_differential.suite import stateful_campaign
            report = stateful_campaign(args.output, args.cases, args.seed)
        elif args.mutations:
            from solidity_differential.mutations import mutation_campaign
            report = mutation_campaign(args.output, args.mutant)
        elif args.reduce:
            from solidity_differential.reduce import reduce_failure
            report = reduce_failure(args.output, args.reduce_seconds)
        elif args.programs:
            from solidity_differential.programs import generated_campaign
            report = generated_campaign(args.output, args.programs, args.cases, args.seed)
        elif args.replay:
            cases = json.loads((args.output / "model-cases.json").read_text())
            manifest = json.loads((args.output / "manifest.json").read_text())
            if hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest() != manifest["casesSha256"]:
                raise HarnessError("replay cases changed")
            report = execute(args.output, cases)
        else:
            if not args.config:
                parser.error("--config is required unless replaying")
            report = campaign(args.config, args.output.resolve(), args.cases, args.seed)
    except (HarnessError, ValueError, KeyError, OSError) as error:
        print(f"HARNESS ERROR: {error}", file=sys.stderr)
        return 2
    print(json.dumps({k: v for k, v in report.items() if k != "divergences"}))
    if args.reduce:
        return 0  # success means the original divergence was preserved
    if report["divergences"]:
        print(f"DIVERGENCE: inspect the reports in {args.output}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
