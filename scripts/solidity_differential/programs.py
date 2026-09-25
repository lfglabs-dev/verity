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
    guard = ""
    error_declaration = ""
    def guard_call(left, right):
        if "require_error" in spec:
            name = spec["require_error"]
            arguments = f"{left}, {right}" if spec["error_arguments"] else ""
            return f'require({left} > {right}, {name}({arguments}));'
        message = json.dumps(spec["require_message"], ensure_ascii=False)
        return f'require({left} > {right}, unicode{message});'
    has_guard = spec.get("require_message") is not None or "require_error" in spec
    if "require_error" in spec:
        parameters = "uint256 left, uint256 right" if spec["error_arguments"] else ""
        error_declaration = f'error {spec["require_error"]}({parameters});'
    if has_guard:
        guard = guard_call(x, "y")
    helper = ""
    if spec["helper"]:
        guard_helper = ""
        if has_guard:
            guard_helper = f'''function check(uint256 x, uint256 y) internal pure returns (uint256) {{
        {guard_call("x", "y")}
        return x;
    }}'''
            guard = f'uint256 checked = L.check({x}, y);'
        helper = f'''library L {{
    {guard_helper}
    function work(uint{bits} x, uint{bits} y) internal pure returns (uint{bits}) {{
        return {render_expr(spec['expression'], bits)};
    }}
}}'''
        expr = f"L.work(uint{bits}({x}), uint{bits}(y))"
    return f'''// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
struct Mkt {{ uint256 ignored; uint128[] ignoredArray; uint256 {member}; }}
{error_declaration}
{helper}
contract C {{
    function f(Mkt memory {market}, uint256 {x}, uint256 y) external pure returns (uint256, uint256, uint256) {{
        {guard}
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
    # Preserve every original arithmetic program, then add guarded programs.
    # Each guarded program retains all three equivalent extraction/name forms.
    for i in range(3 * count):
        bits = [8, 16, 128, 248, 256][i % 5]
        tree = expression(rng, 2, bits)
        # First five explicitly exercise each checked width, especially uint248.
        if i < 5:
            tree = {"kind": "binary", "op": "*", "left": {"kind": "x"}, "right": {"kind": "y"}}
        reference = None
        for variant in (0, 1, 2):
            spec = {"bits": bits, "expression": tree, "renamed": variant == 1, "helper": variant != 0, "projection_collision": variant == 2}
            if count <= i < 2 * count:
                spec["require_message"] = ["", "échec", "x" * 33][(i - count) % 3]
            elif i >= 2 * count:
                kind = (i - 2 * count) % 3
                spec["require_error"] = ["EmptyFailure", "Failure", "AnErrorWhoseSignatureCrossesAThirtyTwoByteWordBoundary"][kind]
                spec["error_arguments"] = kind != 0
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
                divergence = {"metamorphic": str(directory), "reference": str(reference_dir),
                              "rows": [{"line": k, "reference": a, "variant": b} for k, (a, b)
                                       in enumerate(zip(reference.splitlines(), rows.splitlines())) if a != b]}
                write_json(output / "metamorphic-divergence.json", divergence)
                return {"programs": len(reports), "divergences": [divergence]}
            reference, reference_dir = rows, directory
    return {"programs": len(reports), "cases": sum(r["cases"] for r in reports), "divergences": []}


def stateful_scalar_source(original, variant):
    """Equivalent source forms for the handwritten scalar sequence instrument.

    These are not accepted-import claims. Each form is compiled by solc and
    compared to the same model on identical generated transaction sequences.
    """
    if variant == 'baseline':
        return original
    event_line = '        emit Changed(old, value);\n'
    if event_line in original:
        if original.count(event_line) != 1:
            raise ValueError('nonunique event source anchor')
        plain = original.replace(event_line, '')
        return stateful_scalar_source(plain, variant).replace(
            'return old;', 'emit Changed(old, value); return old;')
    before = '''        old = stored;
        stored = value;
        return old;'''
    replacements = {
        'scoped': '''        { uint256 previous = stored; old = previous; }
        { uint256 next = value; stored = next; }
        return old;''',
        'early-return': '''        old = stored;
        if (value == 0) { stored = 0; return old; }
        stored = value;
        return old;''',
    }
    if variant not in replacements or original.count(before) != 1:
        raise ValueError('unknown stateful variant or nonunique source anchor')
    return original.replace(before, replacements[variant])
