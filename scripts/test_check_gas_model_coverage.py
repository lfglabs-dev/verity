#!/usr/bin/env python3
"""The static gas model prices every stack-only arithmetic, comparison and bitwise builtin.

`check_gas.py coverage` only scans Yul that CI generates, so a builtin the compiler can emit
but no example contract uses yet (e.g. `signextend` for intN arguments) goes unpriced and
falls back to `unknownCallCost` (50000) until the first contract that emits it fails CI.
"""
from __future__ import annotations

import sys
import unittest
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import check_gas_model_coverage as coverage

# Yul's EVM dialect: the opcodes that only read and write the stack.
STACK_ONLY_BUILTINS = {
    "add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp", "addmod", "mulmod",
    "signextend", "lt", "gt", "slt", "sgt", "eq", "iszero",
    "and", "or", "xor", "not", "byte", "shl", "shr", "sar",
}


class StaticGasModelCoverageTests(unittest.TestCase):
    def test_every_stack_only_builtin_is_modeled(self) -> None:
        self.assertEqual(STACK_ONLY_BUILTINS - coverage.load_modeled_calls(), set())


if __name__ == "__main__":
    unittest.main()
