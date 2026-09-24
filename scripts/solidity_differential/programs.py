"""Small typed source programs; solc/EVM supplies the expected behavior."""
import copy
import json
from pathlib import Path
import random

from .engine import campaign, write_json


def expression(rng, depth, bits):
    if depth == 0 or rng.randrange(4) == 0:
        return {"kind": rng.choice(["x", "y", "literal"]), "value": rng.choice([0, 1, 2, (1 << bits) - 1])}
    return {"kind": "binary", "op": rng.choice(["+", "-", "*", "/"]),
            "left": expression(rng, depth - 1, bits), "right": expression(rng, depth - 1, bits)}


def render_expr(node, bits, x="x", y="y"):
    ty = f"uint{bits}"
    if node["kind"] == "binary":
        return f'({render_expr(node["left"], bits, x, y)} {node["op"]} {render_expr(node["right"], bits, x, y)})'
    if node["kind"] == "literal":
        return f'{ty}({node["value"]})'
    return f'{ty}({x if node["kind"] == "x" else y})'


def source(spec):
    bits = spec["bits"]
    x = "_verity_slice_tmp_0" if spec["renamed"] else "x"
    member = "tmp_0" if spec.get("projection_collision") else "maturity"
    market = "_verity_slice" if spec.get("projection_collision") else "m"
    expr = render_expr(spec["expression"], bits, x)
    helper = ""
    if spec["helper"]:
        helper = f'''library L {{
    function work(uint{bits} x, uint{bits} y) internal pure returns (uint{bits}) {{
        return {render_expr(spec['expression'], bits)};
    }}
}}'''
        expr = f"L.work(uint{bits}({x}), uint{bits}(y))"
    return f'''// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
struct Mkt {{ uint256 ignored; uint128[] ignoredArray; uint256 {member}; }}
{helper}
contract C {{
    function f(Mkt memory {market}, uint256 {x}, uint256 y) external pure returns (uint256, uint256, uint256) {{
        uint256 stamp = {market}.{member};
        uint{bits} a = {expr};
        uint{bits} b = stamp < {x} ? a : uint{bits}(y);
        return (uint256(a), uint256(b), stamp);
    }}
}}
'''


def write_program(directory, spec):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "Slice.sol").write_text(source(spec))
    write_json(directory / "program.json", spec)
    config = {"project": ".", "entry": "Slice.sol", "contract": "C", "function": "f",
              "param_types": ["struct Mkt", "uint256", "uint256"],
              "variables": {"x": 256, "y": 256, "maturity": 256},
              "arguments": {"_verity_slice.tmp_0" if spec.get("projection_collision") else "m.maturity": "maturity", "_verity_slice_tmp_0" if spec["renamed"] else "x": "x", "y": "y"},
              "storage": [], "corpus": "corpus.json"}
    write_json(directory / "fixture.json", config)
    write_json(directory / "corpus.json", [{"name": "zero", "x": "0", "y": "0", "maturity": "0"},
               {"name": "small", "x": "3", "y": "2", "maturity": "7"},
               {"name": "wrap-product", "x": str(1 << 128), "y": str(1 << 128), "maturity": "1"}])
    return directory / "fixture.json"


def smaller_expressions(node):
    if node["kind"] == "binary":
        yield node["left"]
        yield node["right"]
        for field in ("left", "right"):
            for replacement in smaller_expressions(node[field]):
                result = copy.deepcopy(node)
                result[field] = replacement
                yield result
    if node != {"kind": "literal", "value": 0}:
        yield {"kind": "literal", "value": 0}


def generated_campaign(output, count, cases, seed):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    rng = random.Random(seed)
    reports = []
    for i in range(count):
        bits = [8, 16, 128, 248, 256][i % 5]
        tree = expression(rng, 2, bits)
        # First five explicitly exercise each checked width, especially uint248.
        if i < 5:
            tree = {"kind": "binary", "op": "*", "left": {"kind": "x"}, "right": {"kind": "y"}}
        reference = None
        for variant in (0, 1, 2):
            spec = {"bits": bits, "expression": tree, "renamed": variant == 1, "helper": variant != 0, "projection_collision": variant == 2}
            directory = output / f"program-{i}-{variant}"
            fixture = write_program(directory, spec)
            report = campaign(fixture, directory / "run", cases, seed + i)
            reports.append({"program": i, "variant": variant, **{k: v for k, v in report.items() if k != "divergences"}})
            write_json(output / "program-results.json", reports)
            if report["divergences"]:
                return {"programs": len(reports), "divergences": report["divergences"]}
            # Renaming + helper extraction must preserve the observed behavior.
            rows = (directory / "run/out/source.txt").read_text()
            if reference is not None and reference != rows:
                return {"programs": len(reports), "divergences": [{"metamorphic": str(directory)}]}
            reference = rows
    return {"programs": len(reports), "cases": sum(r["cases"] for r in reports), "divergences": []}
