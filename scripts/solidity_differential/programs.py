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


def stateful_environment_source(original, variant):
    """Equivalent context reads, each imported from its own generated source."""
    if variant == 'baseline':
        return original
    before = 'return (msg.sender, address(this), block.timestamp, block.number, block.chainid);'
    if original.count(before) != 1:
        raise ValueError('nonunique environment return anchor')
    if variant == 'bindings':
        return original.replace(before, '''address sender = msg.sender;
        address self = address(this);
        uint256 timestamp = block.timestamp;
        uint256 number = block.number;
        uint256 chain = block.chainid;
        return (sender, self, timestamp, number, chain);''')
    if variant == 'helpers':
        library = '''library EnvironmentContext {
    function sender() internal view returns (address) { return msg.sender; }
    function self() internal view returns (address) { return address(this); }
    function timestamp() internal view returns (uint256) { return block.timestamp; }
    function number() internal view returns (uint256) { return block.number; }
    function chain() internal view returns (uint256) { return block.chainid; }
}
'''
        return original.replace('contract SequenceFixture {', library + 'contract SequenceFixture {').replace(
            before, 'return (EnvironmentContext.sender(), EnvironmentContext.self(), EnvironmentContext.timestamp(), EnvironmentContext.number(), EnvironmentContext.chain());')
    raise ValueError('unknown environment variant: ' + variant)


def stateful_storage_source(original, variant):
    """Equivalent packed scalar writes/deletes, imported independently per variant."""
    if variant == 'baseline':
        return original
    writes = """low = uint128(value);
        high = uint128(value / 2);
        owner = msg.sender;
        tag = uint96(value);
        stored = value;"""
    deletes = """delete low;
        delete stored;"""
    if original.count(writes) != 1 or original.count(deletes) != 1:
        raise ValueError('nonunique storage source anchors')
    if variant == 'bindings':
        return original.replace(writes, """uint128 nextLow = uint128(value);
        uint128 nextHigh = uint128(value / 2);
        address nextOwner = msg.sender;
        uint96 nextTag = uint96(value);
        low = nextLow;
        high = nextHigh;
        owner = nextOwner;
        tag = nextTag;
        stored = value;""")
    if variant == 'reordered':
        # Disjoint fields, including siblings sharing a physical word: reordering
        # must preserve exactly the same resulting bytes and observations.
        return original.replace(writes, """stored = value;
        tag = uint96(value);
        owner = msg.sender;
        high = uint128(value / 2);
        low = uint128(value);""").replace(deletes, """delete stored;
        delete low;""")
    raise ValueError('unknown storage variant: ' + variant)


def stateful_storage_word_source(original, variant, kind):
    """Equivalent void/bytes32 assignments, preserving each fixture's ABI."""
    if kind not in ('void', 'bytes'):
        raise ValueError('unknown storage word fixture: ' + kind)
    if variant == 'baseline':
        return original
    expression = 'value' if kind == 'void' else 'bytes32(value)'
    before = 'stored = ' + expression + ';'
    if original.count(before) != 1:
        raise ValueError('nonunique storage word assignment anchor')
    if variant == 'bindings':
        ty = 'uint256' if kind == 'void' else 'bytes32'
        after = ty + ' next = ' + expression + ';\n        stored = next;'
    elif variant == 'expression':
        after = 'stored = ' + ('value + 0' if kind == 'void' else 'bytes32(value + 0)') + ';'
    else:
        raise ValueError('unknown storage word variant: ' + variant)
    return original.replace(before, after)


def stateful_mapping_source(original, variant):
    """Equivalent mapping assignments with separately imported source variants."""
    if variant == 'baseline':
        return original
    writes = """balances[msg.sender] = uint128(value);
        authorized[msg.sender][address(this)] = true;
        consumed[msg.sender][bytes32(value)] = uint128(value);
        words[value] = bytes32(value);"""
    if original.count(writes) != 1:
        raise ValueError('nonunique mapping assignment anchor')
    if variant == 'bindings':
        replacement = """address sender = msg.sender;
        address self = address(this);
        uint128 narrow = uint128(value);
        bytes32 word = bytes32(value);
        bool allowed = true;
        balances[sender] = narrow;
        authorized[sender][self] = allowed;
        consumed[sender][word] = narrow;
        words[value] = word;"""
    elif variant == 'reordered':
        replacement = """words[value] = bytes32(value);
        consumed[msg.sender][bytes32(value)] = uint128(value);
        authorized[msg.sender][address(this)] = true;
        balances[msg.sender] = uint128(value);"""
    else:
        raise ValueError('unknown mapping variant: ' + variant)
    return original.replace(writes, replacement)


def stateful_short_circuit_source(original, variant):
    """Same Solidity evaluations expressed with lazy conditionals or De Morgan laws."""
    if variant == 'baseline':
        return original
    replacements = {
        'conditional': {
            'value == 0 || 100 / value > 1': 'value == 0 ? true : 100 / value > 1',
            'value != 0 && 100 / value > 1': 'value != 0 ? 100 / value > 1 : false',
            'value == 7 || guarded(value)': 'value == 7 ? true : guarded(value)',
            '(value == 0 || accepted[msg.sender]) && (value == 7 ? true : guarded(value))':
                '(value == 0 ? true : accepted[msg.sender]) ? (value == 7 ? true : guarded(value)) : false',
            'false || 100 / divisor > 1': 'false ? true : 100 / divisor > 1',
            'true || 100 / divisor > 1': 'true ? true : 100 / divisor > 1',
            'false && accepted[msg.sender]': 'false ? accepted[msg.sender] : false',
        },
        'de-morgan': {
            'value == 0 || 100 / value > 1': '(((value == 0) == false) && ((100 / value > 1) == false)) == false',
            'value != 0 && 100 / value > 1': '(((value != 0) == false) || ((100 / value > 1) == false)) == false',
            'value == 7 || guarded(value)': '(((value == 7) == false) && (guarded(value) == false)) == false',
            'value == 0 || accepted[msg.sender]': '(((value == 0) == false) && (accepted[msg.sender] == false)) == false',
            'false || 100 / divisor > 1': '((false == false) && ((100 / divisor > 1) == false)) == false',
            'true || 100 / divisor > 1': '((true == false) && ((100 / divisor > 1) == false)) == false',
            'false && accepted[msg.sender]': '((false == false) || (accepted[msg.sender] == false)) == false',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if before not in original:
            raise ValueError(f'missing short-circuit source anchor: {before}')
        original = original.replace(before, after)
    return original


def scalar_abi_source(source, variant):
    """Equivalent scalar ABI programs, retaining selectors and parameter types."""
    if variant == 'baseline':
        return source
    if variant == 'renamed':
        import re
        for old, new in [('value', 'argument'), ('full', 'whole'),
                         ('narrow', 'small'), ('account', 'owner'), ('flag', 'enabled')]:
            source = re.sub(r'\b' + old + r'\b', new, source)
        return source
    if variant == 'bindings':
        import re
        source, count = re.subn(r'returns \((uint[0-9]+|address|bool)\) \{ return value; \}',
            lambda m: f'returns ({m[1]}) {{ {m[1]} copy = value; return copy; }}', source)
        if count != 7:
            raise ValueError('ABI binding variant requires seven echo roots')
        return source.replace('return (full, narrow, account, flag);',
            'uint256 copy = full; return (copy, narrow, account, flag);')
    raise ValueError(f'unknown scalar ABI variant: {variant}')


def static_struct_abi_source(source, variant):
    """Equivalent programs preserving eager-memory/lazy-calldata read order."""
    if variant == 'baseline':
        return source
    if variant == 'renamed':
        import re
        for old, new in [('pair', 'input'), ('pad', 'prefix'),
                         ('small', 'leaf'), ('flag', 'enabled')]:
            source = re.sub(r'\b' + old + r'\b', new, source)
        return source
    if variant == 'bindings':
        anchor = 'return pair.small;'
        if source.count(anchor) != 2:
            raise ValueError('static struct binding variant requires two reads')
        return source.replace(anchor, 'uint8 copy = pair.small; return copy;')
    raise ValueError(f'unknown static struct ABI variant: {variant}')


def stateful_imported_event_source(original, variant, narrow=False):
    if variant == 'baseline':
        return original
    if variant == 'renamed':
        return original.replace('stored', 'amount').replace('value', 'quantity')
    if narrow and variant == 'reordered':
        before = 'stored = value;\n        emit Narrow(value, value);'
        after = 'emit Narrow(value, value);\n        stored = value;'
        if original.count(before) != 1:
            raise ValueError('missing narrow event order anchor')
        return original.replace(before, after)
    if not narrow and variant == 'bindings':
        original = original.replace('emit Notices.Changed(msg.sender,',
            'address emitter = msg.sender;\n        emit Notices.Changed(emitter,')
        before = 'emit Detail(low, middle, value, address(this), accepted, bytes32(value));'
        if original.count(before) != 1:
            raise ValueError('missing event binding anchor')
        return original.replace(before, 'address owner = address(this);\n        emit Detail(low, middle, value, owner, accepted, bytes32(value));')
    raise ValueError(variant)


def scalar_array_abi_source(source, variant):
    """Equivalent full-ABI programs; preserve selectors and validation order."""
    if variant == 'baseline':
        return source
    if variant == 'renamed':
        import re
        if len(re.findall(r'\bvalues\b', source)) != 7:
            raise ValueError('scalar-array rename requires one field and six reads')
        return re.sub(r'\bvalues\b', 'payload', source)
    if variant == 'bindings':
        import re
        source, count = re.subn(r'return (box\.values(?:\[[01]\]|\.length));',
            lambda m: 'uint256 copied = ' + m[1] + '; return copied;', source)
        if count != 6:
            raise ValueError('scalar-array bindings require six reads')
        return source
    raise ValueError(f'unknown scalar-array ABI variant: {variant}')


def market_abi_source(source, variant):
    """Equivalent Market wrappers, retaining the pinned interface verbatim."""
    if variant == 'baseline':
        return source
    if variant == 'condition':
        anchor = 'require(flag != 0, "first");'
        if source.count(anchor) != 12:
            raise ValueError('Market variant requires all twelve source guards')
        return source.replace(anchor, 'require(0 != flag, "first");')
    if variant == 'collision':
        anchor = 'require(flag != 0, "first");'
        if source.count(anchor) != 12:
            raise ValueError('Market collision variant requires twelve source guards')
        return source.replace(anchor,
            'uint256 _verity_slice_tmp_0_memory = flag; '
            'require(_verity_slice_tmp_0_memory != 0, "first");')
    if variant == 'bindings':
        anchors = [('market.midnight', 'address'), ('market.maturity', 'uint256'),
                   ('market.collateralParams[0].token', 'address'),
                   ('market.collateralParams[1].token', 'address'), ('market.collateralParams.length', 'uint256')]
        for expression, ty in anchors:
            anchor = 'return ' + expression + ';'
            if source.count(anchor) != 2:
                raise ValueError('Market binding variant requires two roots per expression')
            source = source.replace(anchor, ty + ' copied = ' + expression + '; return copied;')
        return source
    raise ValueError(f'unknown Market ABI variant: {variant}')


def multiple_dynamic_abi_source(source, variant):
    """Equivalent programs with two independent ABI roots."""
    if variant == 'baseline':
        return source
    if variant == 'members':
        return source.replace('values', 'payload').replace('tag', 'marker')
    if variant == 'bindings':
        for side in ('left', 'right'):
            anchor = f'return {side}.values[0];'
            if source.count(anchor) != 2:
                raise ValueError('multiple-root binding anchor must occur in both locations')
            source = source.replace(anchor, f'uint256 result = {side}.values[0]; return result;')
        return source
    if variant == 'condition':
        anchor = 'require(flag != 0, "first");'
        if source.count(anchor) != 4:
            raise ValueError('four multiple-root guards required')
        return source.replace(anchor, 'require(0 != flag, "first");')
    raise ValueError(f'unknown multiple-root variant: {variant}')


def abi_event_variants(original):
    """Equivalent ABI, lexical-scope and event compositions for real A/B/C tests."""
    renamed = original.replace('uint256 tag =', 'uint256 decodedTag =').replace(
        'uint256 value =', 'uint256 decodedValue =').replace('stored = value;',
        'stored = decodedValue;').replace('tag, value);', 'decodedTag, decodedValue);').replace(
        'return value;', 'return decodedValue;')
    scoped = original.replace('        stored = value;', '        { stored = value; }').replace(
        '        emit Decoded(msg.sender, tag, value);',
        '        { emit Decoded(msg.sender, tag, value); }')
    lexical = original.replace('        stored = value;',
        '        { uint256 value = box.values[0]; { stored = value; } }').replace(
        '        return value;', '        { { return value; } }')
    return [('baseline', original), ('renamed', renamed), ('scoped', scoped), ('lexical', lexical)]


def reference_argument_variants(original):
    """Equivalent internal reference calls, preserving the external ABI."""
    import re
    renamed = original
    for old, new in [('box', 'argument'), ('nested', 'relay'),
                     ('readCalldata', 'borrowedRead'), ('readStatic', 'fixedRead')]:
        renamed = re.sub(r'\b' + old + r'\b', new, renamed)
    anchor = 'return box.first();'
    if original.count(anchor) != 1:
        raise ValueError('reference receiver anchor must be unique')
    explicit = original.replace(anchor, 'return ReferenceReaders.first(box);')
    guard = 'require(flag != 0, "first");'
    if original.count(guard) != 1:
        raise ValueError('reference guard anchor must be unique')
    guarded = original.replace(guard, 'require(0 != flag, "first");')
    return [('baseline', original), ('renamed', renamed),
            ('explicit', explicit), ('guarded', guarded)]


def abi_hashing_variants(original):
    """Equivalent ABI hashing sources; pinned IdLib remains unchanged."""
    import re
    renamed = original
    for old, new in [('market', 'inputMarket'), ('value', 'inputValue'),
                     ('left', 'first'), ('right', 'second')]:
        renamed = re.sub(r'\b' + old + r'\b', new, renamed)
    call = 'return IdLib.toId(market);'
    if original.count(call) != 1:
        raise ValueError('IdLib call anchor must be unique')
    receiver = original.replace('contract AbiHashing {',
        'contract AbiHashing {\n    using IdLib for Market;').replace(call, 'return market.toId();')
    bound, count = re.subn(r'return (keccak256\([^\n]+\));',
        r'bytes32 digest = \1; return digest;', original)
    if count < 10:
        raise ValueError('hash binding variant omitted source expressions')
    return [('baseline', original), ('renamed', renamed), ('receiver', receiver), ('bound', bound)]


def stateful_if_else_source(original, variant):
    """Same control flow with inverted conditions and swapped branches, or ternaries."""
    if variant == 'baseline':
        return original
    replacements = {
        'inverted': {
            'if (top >= 192) return 3;': 'if ((top >= 192) == false) {} else return 3;',
            'if (low / 2 * 2 != low) {\n'
            '            require(low > 1, "small odd");\n'
            '        } else {\n'
            '            require(low > 7 || low == 0, "small even");\n'
            '        }':
            'if (low / 2 * 2 == low) {\n'
            '            require(low > 7 || low == 0, "small even");\n'
            '        } else {\n'
            '            require(low > 1, "small odd");\n'
            '        }',
            'if (top >= 128) {\n'
            '            credit[msg.sender] = credit[msg.sender] + top;\n'
            '        } else {\n'
            '            credit[msg.sender] = top;\n'
            '            counter = counter + 1;\n'
            '        }':
            'if (top < 128) {\n'
            '            credit[msg.sender] = top;\n'
            '            counter = counter + 1;\n'
            '        } else {\n'
            '            credit[msg.sender] = credit[msg.sender] + top;\n'
            '        }',
            'if (counter > last) {': 'if ((counter <= last) == false) {',
            'if (counter > 3) return (counter, last, credit[msg.sender]);\n'
            '        return (last, counter, 0);':
            'if (counter <= 3) return (last, counter, 0);\n'
            '        return (counter, last, credit[msg.sender]);',
        },
        'ternary': {
            'if (half > 50) {\n'
            '            uint256 capped = half - 50;\n'
            '            return capped;\n'
            '        }\n'
            '        return half;': 'return half > 50 ? half - 50 : half;',
            'last = tier(top);': 'last = top >= 192 ? 3 : top >= 64 ? 2 : top == 0 ? 0 : 1;',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if before not in original:
            raise ValueError(f'missing if/else source anchor: {before}')
        original = original.replace(before, after)
    return original


def stateful_numeric_literal_source(fixture: str, variant: str) -> str:
    """Keep exact unit/rational values while varying their source spellings."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        source = re.sub(r'\bx\b', 'amount', fixture)
        for old, new in [('WAD', 'UNIT'), ('DAY', 'DAY_UNIT'), ('DOUBLE_DAY', 'PAIR_DAYS')]:
            source = re.sub(r'\b' + old + r'\b', new, source)
        return source
    if variant == 'normalized':
        replacements = {
            '1 seconds': '1', '2 minutes': '120', '3 hours': '10800',
            '4 days': '345600', '5 weeks': '3024000', '0.5 hours': '1800',
            '.5 hours': '1800', '1.25 days': '108000', '7 wei': '7', '8 gwei': '8000000000',
            '9 ether': '9000000000000000000', '0.01e18': '10000000000000000',
            '0.000014e18': '14000000000000', '1e-3 ether': '1000000000000000',
            '2E3': '2000', '0x20': '32', '1_000': '1000', '0x2_0': '32', '1 weeks': '604800',
            '100 * 365 days': '3153600000',
            '1 days': '86400', '1e18': '1000000000000000000',
        }
        source = fixture
        for old, new in replacements.items():
            if old not in source:
                raise RuntimeError(f'missing numeric fixture anchor: {old}')
            source = source.replace(old, new)
        return source
    raise ValueError(f'unknown numeric literal variant: {variant}')


def stateful_constant_array_source(fixture: str, variant: str) -> str:
    """Preserve array constants, index and panic while varying source spelling."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        for old, new in [('FIRST', 'START'), ('LAST', 'END'), ('x', 'index')]:
            fixture = re.sub(r'\b' + old + r'\b', new, fixture)
        return fixture
    if variant == 'normalized':
        replacements = {'uint256 constant FIRST = 1;': 'uint256 constant FIRST = 0x1;',
                        'uint256 constant LAST = 8;': 'uint256 constant LAST = 0x8;',
                        '[FIRST, 2, 3, 4, 5, 6, 7, LAST]': '[FIRST, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, LAST]'}
        for before, after in replacements.items():
            if before not in fixture:
                raise ValueError(f'missing constant-array anchor: {before}')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown constant array variant: {variant}')


def stateful_modulo_source(fixture: str, variant: str) -> str:
    """Compare unsigned remainder with its exact quotient identity."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        return re.sub(r'\bx\b', 'amount', fixture)
    if variant == 'quotient':
        # Preserve the zero-divisor probe verbatim: solc can retain different
        # SLOADs for the expanded quotient despite identical revert bytes.
        # Metamorphic equivalence includes touched slots, not just results.
        if fixture.count('7 % (value - value)') != 1:
            raise ValueError('missing exact modulo zero-divisor probe')
        replacements = {
            'x % 10': '(x - (x / 10) * 10)',
            'uint8(x) % uint8(7)': '(uint8(x) - (uint8(x) / uint8(7)) * uint8(7))',
        }
        for before, after in replacements.items():
            if before not in fixture:
                raise ValueError(f'missing modulo fixture anchor: {before}')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown modulo variant: {variant}')


def stateful_default_local_source(fixture: str, variant: str) -> str:
    """Compare implicit scalar defaults to explicit defaults and renamed locals."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        for old in ('initial', 'small', 'previousCollateralToken', 'enabled', 'digest'):
            fixture = re.sub(r'\b' + old + r'\b', old + '_renamed', fixture)
        return fixture
    if variant == 'explicit':
        for declaration, count, value in (
            ('uint256 initial;', 1, '0'), ('uint8 small;', 1, '0'),
            ('address previousCollateralToken;', 2, 'address(0)'),
            ('bool enabled;', 1, 'false'), ('bytes32 digest;', 1, 'bytes32(0)')):
            if fixture.count(declaration) != count:
                raise ValueError(f'default-local anchor count changed: {declaration}')
            fixture = fixture.replace(declaration, declaration[:-1] + ' = ' + value + ';')
        return fixture
    raise ValueError(f'unknown default-local variant: {variant}')


def stateful_local_write_source(fixture: str, variant: str) -> str:
    """Keep local assignment, shadowing and deletion semantics unchanged."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('current', 'small', 'previousCollateralToken', 'enabled', 'digest', 'local')
        # Preserve strings (especially revert bytes) and comments verbatim.
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda match: match.group(0) + '_renamed'
                      if match.group(0) in names else match.group(0), fixture)
    if variant == 'explicit-zero':
        anchor = 'delete current;'
        if fixture.count(anchor) != 1:
            raise ValueError('local delete anchor changed')
        return fixture.replace(anchor, 'current = 0;')
    raise ValueError(f'unknown local-write variant: {variant}')


def stateful_invariant_for_source(fixture: str, variant: str) -> str:
    """Preserve loop bounds, checked increments and early-return behavior."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('total', 'bound', 'i', 'j')
        # Preserve strings (especially revert bytes) and comments verbatim.
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda match: match.group(0) + '_renamed'
                      if match.group(0) in names else match.group(0), fixture)
    if variant == 'assignment-step':
        for old, new in (('i++)', 'i += 1)'), ('j++)', 'j += 1)')):
            if fixture.count(old) != 1:
                raise ValueError(f'loop step anchor changed: {old}')
            fixture = fixture.replace(old, new)
        return fixture
    raise ValueError(f'unknown invariant-for variant: {variant}')


def abi_length_for_source(source: str, variant: str) -> str:
    """Equivalent ABI-length loops with the complete original malformed matrix."""
    if variant == 'baseline':
        return source
    if variant == 'renamed':
        import re
        for name in ('box', 'total', 'index'):
            source = re.sub(r'\b' + name + r'\b', name + '_renamed', source)
        return source
    if variant == 'assignment-step':
        anchor = 'index++)'
        if source.count(anchor) != 2:
            raise ValueError('ABI-length loop requires both location steps')
        return source.replace(anchor, 'index += 1)')
    raise ValueError(f'unknown ABI-length for variant: {variant}')


def stateful_helper_loop_source(fixture: str, variant: str) -> str:
    """Keep helper returns, caller continuation and exact revert bytes unchanged."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        return _rename_helper_loop(fixture)
    if variant == 'assignment-step':
        if fixture.count('i++)') != 2 or fixture.count('j++)') != 1:
            raise ValueError('helper loop step anchors changed')
        return fixture.replace('i++)', 'i += 1)').replace('j++)', 'j += 1)')
    raise ValueError(f'unknown helper-loop variant: {variant}')


def _rename_helper_loop(fixture: str) -> str:
    import re
    names = ('bound', 'total', 'i', 'j', 'term', 'result')
    token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
    return re.sub(token, lambda m: m.group(0) + '_renamed'
                  if m.group(0) in names else m.group(0), fixture)


def stateful_packed_member_write_source(fixture: str, variant: str) -> str:
    """Preserve packed sibling words, captured alias keys and rollback behavior."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('key', 'selected', 'left', 'right', 'pair', 'outer', 'row')
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-delete':
        for name in ('selected', 'pair'):
            anchor = f'delete {name}.middle;'
            if fixture.count(anchor) != 1:
                raise ValueError('packed member delete anchor changed')
            fixture = fixture.replace(anchor, f'{name}.middle = 0;')
        return fixture
    raise ValueError(f'unknown packed-member variant: {variant}')


def stateful_helper_effect_source(fixture: str, variant: str) -> str:
    """Keep helper effects, caller continuation and exact revert strings intact."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('scratch', 'selected', 'result', 'update')
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-delete':
        for target in ('selected.low', 'entries[1]'):
            anchor = f'delete {target};'
            if fixture.count(anchor) != 1:
                raise ValueError('helper effect delete anchor changed')
            fixture = fixture.replace(anchor, f'{target} = 0;')
        return fixture
    raise ValueError(f'unknown helper-effect variant: {variant}')


def stateful_fixed_array_source(fixture: str, variant: str) -> str:
    """Preserve fixed-array packing, snapshots, bounds and rollback bytes."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('index', 'beforeWrite', 'observed', 'narrow', 'crossing', 'words')
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-delete':
        anchor = 'delete crossing[msg.sender][10];'
        if fixture.count(anchor) != 1:
            raise ValueError('fixed array delete anchor changed')
        return fixture.replace(anchor, 'crossing[msg.sender][10] = 0;')
    raise ValueError(f'unknown fixed-array variant: {variant}')


def stateful_array_write_order_source(fixture: str, variant: str) -> str:
    """Keep RHS/key/index effects, revert priority and capture exactly equal."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('stamp', 'matrix', 'fees', 'first', 'second', 'right', 'trace', 'selected', 'fee')
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'captured-rhs':
        anchor = 'matrix[first(x)][second(x)] = right(x);'
        if fixture.count(anchor) != 1:
            raise ValueError('write-order RHS anchor changed')
        return fixture.replace(anchor, 'uint256 rhs = right(x); matrix[first(x)][second(x)] = rhs;')
    raise ValueError(f'unknown array write-order variant: {variant}')


def stateful_discarded_helper_source(fixture: str, variant: str) -> str:
    """Preserve ignored-result effects, helper returns, events and reverts."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = ('value', 'input', 'bump', 'checked', 'DiscardedHelperLib')
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-result':
        anchor = '        bump(input);'
        if fixture.count(anchor) != 1:
            raise ValueError('discarded helper anchor changed')
        return fixture.replace(anchor, '        uint256 ignored = bump(input);')
    raise ValueError(f'unknown discarded-helper variant: {variant}')


def stateful_encoded_byte_local_source(fixture: str, variant: str) -> str:
    """Equivalent retained byte buffers, alias reads and branch scopes."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'value', 'input', 'digest', 'encoded', 'prefixed', 'aliasBuffer',
                 'first', 'second', 'other', 'rootBytes', 'branchBytes', 'result'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'copy-alias':
        anchor = 'bytes memory aliasBuffer = prefixed;'
        if fixture.count(anchor) != 1:
            raise ValueError('encoded byte alias anchor changed')
        return fixture.replace(anchor, 'bytes memory aliasBuffer = abi.encodePacked(prefixed, hex"");')
    raise ValueError(f'unknown encoded-byte-local variant: {variant}')


def stateful_named_helper_return_source(fixture: str, variant: str) -> str:
    """Equivalent named result defaults, writes, scopes and assembly continuations."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'value', 'input', 'result', 'seed', 'defaultResult', 'early',
                 'continuedAssembly', 'narrowAssembly', 'nested', 'booleanAssembly',
                 'addressAssembly', 'branchAssembly', 'branchValue', 'shadowedAssembly',
                 'shadowedValue', 'zero', 'first', 'second', 'third', 'narrow',
                 'flag', 'who', 'addressValue', 'booleanValue'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-fallthrough':
        anchors = {
            'function defaultResult() internal pure returns (uint256 result) { }':
            'function defaultResult() internal pure returns (uint256 result) { return result; }',
            '        result = result + 3;\n    }':
            '        result = result + 3;\n        return result;\n    }',
            '        result = result + 1;\n    }':
            '        result = result + 1;\n        return result;\n    }',
            '        result = result + 5;\n    }':
            '        result = result + 5;\n        return result;\n    }',
            '        result = result + 6;\n    }':
            '        result = result + 6;\n        return result;\n    }',
            '        result = result + zero;\n    }':
            '        result = result + zero;\n        return result;\n    }',
        }
        for before, after in anchors.items():
            if fixture.count(before) != 1:
                raise ValueError('named helper fallthrough anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown named-helper-return variant: {variant}')


def stateful_yul_numeric_source(fixture: str, variant: str) -> str:
    """Equivalent Yul word literals and pure wrapping addition."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'value', 'input', 'result', 'literal', 'boundary', 'decimal',
                 'hexadecimal', 'wordEdge', 'wrapping', 'combined', 'left', 'middle', 'right'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'normalized':
        replacements = {
            'xor(input, 31)': 'xor(input, 0x1f)',
            'xor(input, 0x20)': 'xor(input, 32)',
            '0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff': str((1 << 256) - 1),
            'add(input, 1)': 'add(1, input)',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('Yul numeric normalization anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown Yul numeric variant: {variant}')


def stateful_solc_0810_source(fixture: str, variant: str) -> str:
    """Equivalent solc 0.8.10 sources with single- and double-quoted imports."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'value', 'managementFee', 'feeSplit', 'input', 'tvl', 'fee', 'receiver'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'double-quoted':
        replacements = {
            "import './Solc0810Imported.sol';": 'import "./Solc0810Imported.sol";',
            'uint256 tvl = (input % 1000000) * 365 days + 365 days;':
            'uint256 tvl = ((input % 1000000) + 1) * 365 days;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('solc 0.8.10 double-quoted anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown solc 0.8.10 variant: {variant}')


def stateful_inheritance_source(fixture: str, variant: str) -> str:
    """Equivalent C3 inheritance sources with local renaming and explicit base qualification."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'input', 'seed', 'direct', 'chained', 'bonus', 'x'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'qualified-super':
        replacements = {
            'return super.step(x);': 'return InheritanceRight.step(x);',
            'uint256 bonus = viaVirtual(seed);': 'uint256 bonus = InheritanceRoot.viaVirtual(seed);',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('inheritance qualified-super anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown inheritance variant: {variant}')


def stateful_void_helper_guard_source(fixture: str, variant: str) -> str:
    """Equivalent void-helper and guard sources with local renaming and explicit fallthrough."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'input', 'seed', 'currentEpoch', 'hookZero', 'out', 'snapshot'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-else-and-return':
        replacements = {
            'require(input != 20, "void helper guard rollback");':
            'require(input != 20, "void helper guard rollback");\n        return out;',
            'function _emptyHook(uint256) internal pure returns (uint256) {}':
            'function _emptyHook(uint256) internal pure returns (uint256 zero) { return zero; }',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('void-helper-guards variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown void-helper-guards variant: {variant}')


def stateful_modifier_unchecked_compound_source(fixture: str, variant: str) -> str:
    """Equivalent modifier, unchecked, and compound-assignment sources with local renaming and expanded assignments."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {'input', 'seed', 'slot', 'localAcc', 'assigned', 'wrapMul', 'rawHelper', 'helperOut', 'localMirror', 'echoed', 'raw', 'delta'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-compound':
        replacements = {
            'localAcc += 17;': 'localAcc = localAcc + 17;',
            'localAcc -= 5;': 'localAcc = localAcc - 5;',
            '10 ** 3': '1000',
            '2 ** 8': '256',
            'uint256 echoed = (localMirror = seed + 11) + 6;':
            'localMirror = seed + 11;\n        uint256 echoed = localMirror + 6;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('modifier-unchecked-compound variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown modifier-unchecked-compound variant: {variant}')


def stateful_tuple_helper_source(fixture: str, variant: str) -> str:
    """Equivalent multi-return helper, parameter compound-assignment, and narrow literal event sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'input', 'seed', 'slot', 'gain', 'mgmtFee', 'netGain', 'baseClaim',
            'rate', 'interest', 'claimBasis', 'burnAmount', 'seedBonus',
            'gross', 'fee', 'boosted', 'clearedBasis', 'clearedBurn',
            'splitNet', 'localSecondary', 'feeAdjusted',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'explicit-return-and-literal':
        replacements = {
            'burnAmount = baseClaim;': 'burnAmount = baseClaim;\n        return (claimBasis, burnAmount);',
            'emit NarrowInitialized(type(uint8).max);': 'emit NarrowInitialized(255);',
            '(uint256 splitNet, ) = _splitWithParamCompound(seed + 30, (seed % 9) + 4);':
            '(uint256 splitNet, uint256 unusedBoost) = _splitWithParamCompound(seed + 30, (seed % 9) + 4);',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('tuple-helper variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown tuple-helper variant: {variant}')


def stateful_int256_contract_type_source(fixture: str, variant: str) -> str:
    """Equivalent int256 arithmetic/storage/mapping and contract-type sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'input', 'seed', 'slot', 'candidate', 'fallbackPeer', 'preferCandidate',
            'baseDelta', 'step', 'flipped', 'scaled', 'boundTag', 'wrapProbe',
            'maxEdge', 'minEdge', 'negMin', 'defaultPeer', 'chosen', 'rawSigned',
            'adjusted', 'peerWord', 'one', 'negOne',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-signed-and-cast':
        replacements = {
            'scaled += 4;':
            'scaled = scaled + 4;',
            'scaled -= 2;':
            'scaled = scaled - 2;',
            'IPeer defaultPeer;':
            'IPeer defaultPeer = IPeer(address(0));',
            'signedDeltaBySlot[slot] += adjusted;':
            'signedDeltaBySlot[slot] = signedDeltaBySlot[slot] + adjusted;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('int256-contract-types variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown int256-contract-types variant: {variant}')


def stateful_fn_ptr_struct_delete_modifier_source(fixture: str, variant: str) -> str:
    """Equivalent function-pointer, mapping-struct delete, and post-placeholder modifier sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'input', 'seed', 'slot', 'subKey', 'pickFirst', 'tag',
            'calcFn', 'recordFn', 'pairFn', 'computed', 'p0', 'p1',
            'ord', 'ordSum', 'nestedSum', 'a', 'b', 'val', 'x', 'y',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-delete-and-modifier':
        replacements = {
            'preCounter += tag + 1;':
            'preCounter = preCounter + tag + 1;',
            'postCounter += tag + 2;':
            'postCounter = postCounter + tag + 2;',
            'delete orders[slot];':
            'orders[slot].amount = 0;\n            orders[slot].fee = 0;\n            orders[slot].epoch = 0;',
            'delete nestedOrders[slot][subKey];':
            'nestedOrders[slot][subKey].amount = 0;\n            nestedOrders[slot][subKey].fee = 0;\n            nestedOrders[slot][subKey].epoch = 0;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('fn-ptr-struct-delete-modifier variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown fn-ptr-struct-delete-modifier variant: {variant}')


def stateful_empty_array_bytes_calldata_source(fixture: str, variant: str) -> str:
    """Equivalent empty-body dynamic array return and bytes calldata root parameter sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        renamed = fixture.replace(
            'function getRewardTokens() external view returns (address[] memory) {}',
            'function getRewardTokens() external view returns (address[] memory rewardTokens) {}',
        ).replace(
            'function redeemRewards(bytes calldata) external returns (uint256[] memory) {}',
            'function redeemRewards(bytes calldata ignoredData) external returns (uint256[] memory amounts) {}',
        )
        if renamed == fixture:
            raise ValueError('empty-array-bytes-calldata renamed anchor changed')
        names = {'payload', 'tag', 'len', 'out', 'value'}
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), renamed)
    if variant == 'expanded-length-and-accum':
        replacements = {
            'emptyFlag = (payload.length == 0);':
            'emptyFlag = (len == 0);',
            'totalSeen += len + 1;':
            'totalSeen = totalSeen + len + 1;',
            'lengthByTag[tag] += lastLength + 1;':
            'lengthByTag[tag] = lengthByTag[tag] + lastLength + 1;',
            'totalSeen += lengthByTag[tag];':
            'totalSeen = totalSeen + lengthByTag[tag];',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('empty-array-bytes-calldata variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown empty-array-bytes-calldata variant: {variant}')


def stateful_overload_const_error_cond_tuple_tload_source(fixture: str, variant: str) -> str:
    """Equivalent same-contract overload, constant custom-error arg, conditional tuple, and tload sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'input', 'seed', 'owner', 'spender', 'maturity',
            'start', 'end', 'feeLower', 'feeUpper', 'locked',
            'interpolated', 'baseSlot', 'key1', 'key2', 'slot',
            'value', 'emitEvent', 'ZERO_WORD', 'CBP_SCALE', 'LOCK_BASE_SLOT',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-error-and-accum':
        replacements = {
            'require(input != 19, BoundError(address(0), type(uint8).max, ZERO_WORD));':
            'require(input != 19, BoundError(address(0), 255, 0));',
            'revert BoundError(address(0), type(uint8).max, ZERO_WORD);':
            'revert BoundError(address(0), 255, 0);',
            'approvalCount += 1;':
            'approvalCount = approvalCount + 1;',
            'feeAccumulator += interpolated + (locked ? 1000 : 1) + allowances[owner][spender];':
            'feeAccumulator = feeAccumulator + interpolated + (locked ? 1000 : 1) + allowances[owner][spender];',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('overload-const-error-cond-tuple-tload variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown overload-const-error-cond-tuple-tload variant: {variant}')


def stateful_struct_fixed_array_and_fixed_return_source(fixture: str, variant: str) -> str:
    """Equivalent struct fixed-size array member and root fixed-size array return sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'input', 'id', 'seed', 'writeIdx', 'readIdx', 'snap', 'fees',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-array-and-return':
        replacements = {
            'position[id][msg.sender].credit += uint128(seed);':
            'position[id][msg.sender].credit = position[id][msg.sender].credit + uint128(seed);',
            'delete position[id][msg.sender].fees[1];':
            'position[id][msg.sender].fees[1] = 0;',
            'pool[id].total += seed;':
            'pool[id].total = pool[id].total + seed;',
            'uint16[3] memory fees = settlementFeeCbps[id];\n        return fees;':
            'return [settlementFeeCbps[id][0], settlementFeeCbps[id][1], settlementFeeCbps[id][2]];',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('struct-fixed-array-and-fixed-return variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown struct-fixed-array-and-fixed-return variant: {variant}')


def stateful_msg_data_and_enum_source(fixture: str, variant: str) -> str:
    """Equivalent msg.data / _msgData() and enum support sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'raw', 'mode', 'value', 'r', 'nextR', 'adj', 'msgLen',
            'input', 'rawMode', 'm', 'span', 'current', 'x', 'next', 'adjusted',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-enum-and-msgdata':
        replacements = {
            'return _msgData();':
            'return msg.data;',
            'uint256 msgLen = _msgData().length + msg.data.length;':
            'uint256 msgLen = msg.data.length + _msgData().length;',
            'totalScore += adj + uint256(uint8(nextR)) + msgLen;':
            'totalScore = totalScore + adj + uint256(uint8(nextR)) + msgLen;',
            'totalScore += adj + uint256(uint8(nextR)) + span;':
            'totalScore = totalScore + adj + uint256(uint8(nextR)) + span;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('msg-data-and-enum variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown msg-data-and-enum variant: {variant}')


def stateful_exp_and_bitwise_shift_source(fixture: str, variant: str) -> str:
    """Equivalent exponentiation, bitwise, shift, and compound assignment sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'x', 'y', 'z', 'bitmap', 'bit', 'a', 'b', 'value', 'result', 'candidate',
            'input', 'exp', 'scale', 'sq', 'wrappedPow', 'bitIdx', 'nextMap', 'metric', 's',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-exp-and-bitwise':
        replacements = {
            'nextMap |= uint128(1 << (input % 16));':
            'nextMap = nextMap | uint128(1 << (input % 16));',
            'nextMap &= uint128(0x7fffffffffffffffffffffffffffffff);':
            'nextMap = nextMap & uint128(0x7fffffffffffffffffffffffffffffff);',
            'nextMap ^= ~uint128(input & 0xff);':
            'nextMap = nextMap ^ ~uint128(input & 0xff);',
            'nextMap >>= uint8((input % 2) + 1);':
            'nextMap = nextMap >> uint8((input % 2) + 1);',
            'nextMap <<= uint8(input % 3);':
            'nextMap = nextMap << uint8(input % 3);',
            'metric /= ((input % 3) + 1);':
            'metric = metric / ((input % 3) + 1);',
            'metric %= 1000000007;':
            'metric = metric % 1000000007;',
            's >>= uint8((input % 3) + 1);':
            's = s >> uint8((input % 3) + 1);',
            's <<= 1;':
            's = s << 1;',
            's /= int256(2);':
            's = s / int256(2);',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('exp-and-bitwise-shifts variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown exp-and-bitwise-shifts variant: {variant}')


def stateful_while_clz_and_struct_loc_source(fixture: str, variant: str) -> str:
    """Equivalent bounded while-loop, Yul clz, and struct location/local sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'x', 'r', 'z', 'bitmap', 'value', 'result', 'v', 'bit', 'count',
            'pending', 'acc', 'cfg', 'b', 'idx', 'aliasB', 's', 'cdAlias',
            'memCopy', 'bundle', 'pivot', 'n', 'lastIdx', 'cdLast', 'memFirst',
            'helperScore', 'digest', 'clzMetric', 'halvingMetric', 'popMetric',
            'msbSumMetric', 'metrics', 'input', 'z0', 'nonzero', 'l2a', 'l2b',
            'pc', 'sb', 'delta', 'z1',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-while-and-struct-loc':
        replacements = {
            'bit >>= 1;':
            'bit = bit >> 1;',
            'v &= (v - 1);':
            'v = v & (v - 1);',
            'pending = _clearBit(pending, i);':
            'pending &= ~(1 << i);',
            'Step memory memFirst = bundle.steps[lastIdx - lastIdx];':
            'Step memory memFirst = bundle.steps[0];',
            'totalScore += acc + helperScore;':
            'totalScore = totalScore + acc + helperScore;',
            'totalScore += delta;':
            'totalScore = totalScore + delta;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('while-clz-and-struct-loc variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown while-clz-and-struct-loc variant: {variant}')


def stateful_yul_builtins_and_encode_selector_source(fixture: str, variant: str) -> str:
    """Equivalent Yul arithmetic/bitwise/context builtins and abi.encodeWithSelector sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'result', 'a', 'b', 'base', 'exponent', 'idx', 'word', 'byteIdx',
            'input', 'token', 'recipient', 'amount', 'transferCall', 'aliasCall',
            'd1', 'd2', 'd3', 'd4', 'digest', 'signedA', 'signedB', 'q', 'r',
            'cmpBits', 'powVal', 'pickedByte', 'ext0', 'extWide', 'ctxMix',
            'yulMetric', 'd',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-selector-and-yul':
        replacements = {
            'bytes memory aliasCall = transferCall;\n        bytes32 d1 = keccak256(aliasCall);':
            'bytes32 d1 = keccak256(transferCall);',
            'totalScore += (uint256(digest) & 0xffffffff) + (yulMetric & 0xffffffff);':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + (yulMetric & 0xffffffff);',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('yul-builtins-and-encode-selector variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown yul-builtins-and-encode-selector variant: {variant}')


def stateful_array_string_params_and_context_source(fixture: str, variant: str) -> str:
    """Equivalent dynamic scalar-array/string parameter, string local, selfbalance, and tx.origin sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'result', 'a', 'b', 's', 'vals', 'addrs', 'acc', 'caps', 'input',
            'balA', 'balB', 'balYul', 'origSol', 'origYul', 'baseTag', 'rightTag',
            'combined', 'wrapped', 'strMetric', 'digest', 'ctxMetric', 'amounts',
            'recipients', 'label', 'tag', 'rolling', 'cdSum', 'memSum', 'fullLabel',
            'labelMetric', 'finalDigest', 'metric', 'scale', 'direct', 'memTotal',
            'reasonTag', 'd', 'recipient', 'amount', 'balSum', 'amountsLen',
            'recipientsLen', 'orig',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-array-string-context':
        replacements = {
            'totalScore += (uint256(digest) & 0xffffffff) + ctxMetric;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + ctxMetric;',
            'totalScore += (uint256(finalDigest) & 0xffffffff) + metric;':
            'totalScore = totalScore + (uint256(finalDigest) & 0xffffffff) + metric;',
            'totalScore += metric;':
            'totalScore = totalScore + metric;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('array-string-params-and-context variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown array-string-params-and-context variant: {variant}')


def stateful_bytes_memory_and_abi_encode_call_source(fixture: str, variant: str) -> str:
    """Equivalent bytes memory parameter/helper/local, .length, bytes.concat/string.concat, abi.encodeWithSignature, and abi.encodeCall sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'payload', 'salt', 'recipient', 'amount', 'delta', 'tag', 'pingData',
            'notifyData', 'settleData', 'sigData', 'buf', 'weight', 'a', 'b',
            'input', 'tagWord', 'batch', 'envelope', 'label', 'fullLabel',
            'inlineCallLen', 'inlineSigLen', 'concatLen', 'totalLen', 'bufMetric',
            'digest', 'lengthMetric', 'memPayload', 'cdPayload', 'wrappedMem',
            'copiedCd', 'memMetric', 'cdMetric', 'joined', 'lenSum', 'callData', 'innerHash', 'combined',
            'metric', 'errBuf', 'd', 'errLen', 'account',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-bytes-memory-encode-call':
        replacements = {
            'return string.concat(a, ":", b);':
            'return string(abi.encodePacked(a, ":", b));',
            'totalScore += (uint256(digest) & 0xffffffff) + lengthMetric;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + lengthMetric;',
            'totalScore += (uint256(digest) & 0xffffffff) + metric;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + metric;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('bytes-memory-and-abi-encode-call variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown bytes-memory-and-abi-encode-call variant: {variant}')


def stateful_dynamic_bytes_and_string_return_source(fixture: str, variant: str) -> str:
    """Equivalent dynamic bytes/string root return, _concat(string,string), and modifier post-statement sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'caller', 'amount', 'delta', '_a', '_b', 'payload', 'salt', 'input',
            'label', 'saltWord', 'packed', 'combinedLen', 'digest', 'metric',
            'a', 'b', 'mode', 'lenSum', 'kind', 'memPart', 'cdPart', 'modeTag',
            'signedDelta', 'errLabel', 'd', 'errLen',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-dynamic-return':
        replacements = {
            'return string.concat(a, "-", b);':
            'return string(abi.encodePacked(a, "-", b));',
            'returnCount += 1;':
            'returnCount = returnCount + 1;',
            'totalScore += (delta & 0xffff) + returnCount;':
            'totalScore = totalScore + (delta & 0xffff) + returnCount;',
            'totalScore += (uint256(digest) & 0xffffffff) + metric;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + metric;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1 and before != 'returnCount += 1;':
                raise ValueError('dynamic-bytes-and-string-return variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown dynamic-bytes-and-string-return variant: {variant}')


def stateful_bytes_and_string_storage_source(fixture: str, variant: str) -> str:
    """Equivalent string/bytes storage variable read, write, length, delete, and return sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'delta', 'name_', 'symbol_', 'input', 'branch', 'saltWord', 'nameLen',
            'symLen', 'payLen', 'totalLen', 'digest', 'metric', 'newName',
            'newPayload', 'mode', 'kind', 'combinedLen', 'd', 'errLen', 'lenMetric',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-bytes-string-storage':
        replacements = {
            '_symbol = string.concat(_name, ":tag");':
            '_symbol = string(abi.encodePacked(_name, ":tag"));',
            '_name = string.concat(newName, "-", _symbol);':
            '_name = string(abi.encodePacked(newName, "-", _symbol));',
            'syncCount += 1;':
            'syncCount = syncCount + 1;',
            'totalScore += (delta & 0xffff) + bytes(_name).length + _payload.length;':
            'totalScore = totalScore + (delta & 0xffff) + bytes(_name).length + _payload.length;',
            'totalScore += (uint256(digest) & 0xffffffff) + metric;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + metric;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1 and before != 'syncCount += 1;':
                raise ValueError('bytes-and-string-storage variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown bytes-and-string-storage variant: {variant}')


def stateful_yul_block_mulmod_tstore_source(fixture: str, variant: str) -> str:
    """Equivalent multi-statement Yul block, mulmod/addmod, tstore, and *= compound assignment sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'slot', 'nextValue', 'prevValue', 'current', 'x', 'y', 'denominator',
            'result', 'prod0', 'prod1', 'mm', 'remainder', 'twos', 'inverse',
            'a', 'b', 'modVal', 'out', 'localAcc', 'step', 'm', 'input', 'prev',
            'prevA', 'afterA', 'loaded', 'restoredA', 'modBase', 'solMul', 'solAdd',
            'yulZeroMod', 'bigX', 'bigY', 'bigDenom', 'scaled', 'mixed', 'factor',
            'localProd', 'sVal', 'bucketKey', 'combined', 'digest', 'slotKey',
            'weight', 'denom', 'oldVal', 'safeDenom', 'mVal', 'aVal', 'cur',
            'next', 'finalLock', 'currentLock', 'summary', 'slotA', 'slotB', 'pulseScore',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-yul-mulmod-tstore':
        replacements = {
            'localProd *= factor;':
            'localProd = localProd * factor;',
            'packedScale *= uint128(factor);':
            'packedScale = packedScale * uint128(factor);',
            'narrowCounter *= uint64(factor + 0x100000001);':
            'narrowCounter = narrowCounter * uint64(factor + 0x100000001);',
            'sVal *= -3;':
            'sVal = sVal * -3;',
            'signedMetric *= sVal;':
            'signedMetric = signedMetric * sVal;',
            'bucketMul[bucketKey] *= factor;':
            'bucketMul[bucketKey] = bucketMul[bucketKey] * factor;',
            'weight += 2;':
            'weight += 1 + 1;',
            'totalScore += (uint256(digest) & 0xffffffff) + combined;':
            'totalScore = totalScore + (uint256(digest) & 0xffffffff) + combined;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('yul-block-mulmod-tstore variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown yul-block-mulmod-tstore variant: {variant}')


def stateful_merkle_and_nonces_source(fixture: str, variant: str) -> str:
    """Equivalent extended scalar constants, scratch-space Yul mstore/keccak256, bytes32 shifts, and ++/-- sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'left', 'right', 'value', 'word', 'a', 'b', 'owner', 'nonce', 'current',
            'leafHash', 'leafIndex', 'p0', 'p1', 'currentHash', 'input', 'expectedNonce',
            'afterFirst', 'beforeDec', 'localCounter', 'postInc', 'preInc', 'postDec',
            'preDec', 'narrowLocal', 'narrowPost', 'narrowPre', 'preStep', 'postStep',
            'sDelta', 'sPost', 'sPre', 'cursorSnap', 'boxKey', 'hitBefore', 'hitAfter',
            'g1', 'g2', 'gridBefore', 'gridAfter', 'leaf', 'sib0', 'sib1', 'shiftedMask',
            'merkleOut', 'score', 'summary',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-merkle-and-nonces':
        replacements = {
            '\n        localCounter++;':
            '\n        localCounter += 1;',
            '\n        --localCounter;':
            '\n        localCounter -= 1;',
            'narrowLocal--;':
            'narrowLocal -= 1;',
            'stepCount--;':
            'stepCount -= 1;',
            'signedCursor++;':
            'signedCursor += 1;',
            'boxes[boxKey].misses++;':
            'boxes[boxKey].misses += 1;',
            '--boxes[boxKey].misses;':
            'boxes[boxKey].misses -= 1;',
            'gridNonce[g1][g2]--;':
            'gridNonce[g1][g2] -= 1;',
            'sib0 <<= (input & 7);':
            'sib0 = sib0 << (input & 7);',
            'sib1 >>= ((input >> 3) & 7);':
            'sib1 = sib1 >> ((input >> 3) & 7);',
            'totalScore += (uint256(merkleOut) & 0xffffffff) + score;':
            'totalScore = totalScore + (uint256(merkleOut) & 0xffffffff) + score;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('merkle-and-nonces variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown merkle-and-nonces variant: {variant}')


def stateful_multiproof_mapping_keys_ratifiers_source(fixture: str, variant: str) -> str:
    """Equivalent dynamic memory scalar array allocation/write, extended mapping keys/struct members, and root named Yul return sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'left', 'right', 'value', 'a', 'b', 'slot', 'oldValue', 'proof',
            'proofFlags', 'leaves', 'merkleRoot', 'leavesLen', 'proofFlagsLen',
            'hashes', 'leafPos', 'hashPos', 'proofPos', 'input', 'resultAddr',
            'badLeaves', 'badProof', 'badFlags', 'root', 'ratifierId', 'feed',
            'maxDiff', 'isEnabled', 'delta', 'user', 'nKey', 'mode', 'tSlot',
            'nextActor', 'prevActor', 'loadedActor', 'score', 'exitSlot',
            'dirtyWord', 'r0', 'summary', 'caller',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-multiproof-ratifiers':
        replacements = {
            'narrowKeyScores[nKey] += uint256(maxDiff);':
            'narrowKeyScores[nKey] = narrowKeyScores[nKey] + uint256(maxDiff);',
            'signedKeyScores[delta] += (input & 0x1f) + 1;':
            'signedKeyScores[delta] = signedKeyScores[delta] + (input & 0x1f) + 1;',
            'boolKeyScores[ratifiers[ratifierId].enabled] += 3;':
            'boolKeyScores[ratifiers[ratifierId].enabled] = boolKeyScores[ratifiers[ratifierId].enabled] + 3;',
            'modeKeyScores[mode] += 5;':
            'modeKeyScores[mode] = modeKeyScores[mode] + 5;',
            'feedKeyScores[ratifiers[ratifierId].oracle] += 7;':
            'feedKeyScores[ratifiers[ratifierId].oracle] = feedKeyScores[ratifiers[ratifierId].oracle] + 7;',
            'totalScore += score;':
            'totalScore = totalScore + score;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('multiproof-mapping-keys-ratifiers variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown multiproof-mapping-keys-ratifiers variant: {variant}')


def stateful_udvt_param_assign_hashmarket_source(fixture: str, variant: str) -> str:
    """Equivalent user-defined value types, direct parameter assignment, chained/conditional multi-returns, and dynamic memory array/market hashing sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'c', 'delta', 'cap', 'tokens', 'digest', 'words', 'items', 'step',
            'bonus', 'id', 'raw', 'a', 'b', 'pickChained', 'item', 'tok', 'fac',
            'act', 'th', 'market', 'clockTag', 'itemHashes', 'cdHash', 'memCopy',
            'memHash', 'itemsDigest', 'cw', 'input', 'callerCopy', 'scrubbed',
            'clk', 'clockWord', 'sid', 'shortTag', 'tokHash', 'wordHash',
            'pairVal', 'pairTag', 'combinedDigest', 'addBonus',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-udvt-param-hashmarket':
        replacements = {
            'step = step * 2 + bonus;':
            'step = (step << 1) + bonus;',
            'raw = raw + delta;':
            'raw += delta;',
            'a = a + 7;':
            'a += 7;',
            'totalScore += (uint256(lastDigest) & 0xffff) + market.items.length;':
            'totalScore = totalScore + (uint256(lastDigest) & 0xffff) + market.items.length;',
            'totalScore += delta;':
            'totalScore = totalScore + delta;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('udvt-param-assign-hashmarket variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown udvt-param-assign-hashmarket variant: {variant}')


def stateful_struct_mapping_and_bytes4_interface_source(fixture: str, variant: str) -> str:
    """Equivalent nested struct mappings, bytes4 scalars/casts/bitwise ops, and type(I).interfaceId sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'role', 'account', 'neededRole', 'previousAdminRole',
            'newAdminRole', 'sel', 'maskVal', 'out',
            'maskBytes', 'combined', 'scopeId', 'weightTag', 'delta', 'scoped',
            'w', 'activeBit', 'tag', 'ok', 'scrubbed', 'word32', 'digest',
            'bonus', 'input', 'caller', 'peer', 'branch', 'weightKey',
            'weightNow', 'scopedMetric', 'probeIface', 'ifaceSupported',
            'scrubbedWord', 'roleBit', '_msgSender', '_checkRole',
            '_setRoleAdmin', '_grantRole', '_revokeRole', '_scrubSelector',
            '_syncScopedRole',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-struct-mapping-bytes4':
        replacements = {
            '_roles[role].grantCount += 1;':
            '_roles[role].grantCount = _roles[role].grantCount + 1;',
            'combined ^= type(IERC165Lite).interfaceId;':
            'combined = combined ^ type(IERC165Lite).interfaceId;',
            'scoped.weights[weightTag] += delta + 3;':
            'scoped.weights[weightTag] = scoped.weights[weightTag] + delta + 3;',
            'scoped.grantCount += 1;':
            'scoped.grantCount = scoped.grantCount + 1;',
            'totalScore += delta;':
            'totalScore = totalScore + delta;',
            'totalScore += 999;':
            'totalScore = totalScore + 999;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('struct-mapping-and-bytes4-interface variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown struct-mapping-and-bytes4-interface variant: {variant}')


def stateful_erc2981_holders_arrays_msghash_source(fixture: str, variant: str) -> str:
    """Equivalent ERC2981 whole-struct storage/memory locals, holder .selector, Arrays.unsafeMemoryAccess, and MessageHashUtils sources."""
    if variant == 'baseline':
        return fixture
    if variant == 'renamed':
        import re
        names = {
            'tokenId', 'salePrice', 'royalty', 'feeNumerator', 'denominator',
            'arr', 'pos', 'res', 'messageHash', 'digest', 'validator', 'data',
            'domainSeparator', 'structHash', 'ptr', 's', 'result',
            'sel721', 'sel1155', 'combinedSel', 'ethDigest', 'validatorDigest',
            'typedDigest', 'input', 'candidate', 'fraction', 'mode', 'rcv',
            'amt', 'amounts', 'receivers', 'pickedAmt', 'pickedRcv', 'ss',
            'ssLen', 'sel', 'valDigest', 'delta', 'defFrac',
            '_feeDenominator', '_setDefaultRoyalty', '_deleteDefaultRoyalty',
            '_setTokenRoyalty', '_resetTokenRoyalty', '_unsafeMemoryAccessUint',
            '_unsafeMemoryAccessAddress', '_toEthSignedMessageHash',
            '_toDataWithIntendedValidatorHash', '_toTypedDataHash',
            '_shortStringByteLength',
        }
        token = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_$][A-Za-z0-9_$]*'
        return re.sub(token, lambda m: m.group(0) + '_renamed'
                      if m.group(0) in names else m.group(0), fixture)
    if variant == 'expanded-erc2981-holders-arrays-msghash':
        replacements = {
            'totalScore += (uint256(typedDigest) & 0xffff) + royaltyAmount + uint256(lastSelectorWord & 0xff);':
            'totalScore = totalScore + (uint256(typedDigest) & 0xffff) + royaltyAmount + uint256(lastSelectorWord & 0xff);',
            'totalScore += delta;':
            'totalScore = totalScore + delta;',
            'totalScore += 777;':
            'totalScore = totalScore + 777;',
        }
        for before, after in replacements.items():
            if fixture.count(before) != 1:
                raise ValueError('erc2981-holders-arrays-msghash variant anchor changed')
            fixture = fixture.replace(before, after)
        return fixture
    raise ValueError(f'unknown erc2981-holders-arrays-msghash variant: {variant}')

