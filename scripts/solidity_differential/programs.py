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
        if len(re.findall(r'\bvalues\b', source)) != 5:
            raise ValueError('scalar-array rename requires one field and four reads')
        return re.sub(r'\bvalues\b', 'payload', source)
    if variant == 'bindings':
        import re
        source, count = re.subn(r'return (box\.values\[[01]\]);',
            lambda m: 'uint256 copied = ' + m[1] + '; return copied;', source)
        if count != 4:
            raise ValueError('scalar-array bindings require four reads')
        return source
    raise ValueError(f'unknown scalar-array ABI variant: {variant}')


def market_abi_source(source, variant):
    """Equivalent Market wrappers, retaining the pinned interface verbatim."""
    if variant == 'baseline':
        return source
    if variant == 'condition':
        anchor = 'require(flag != 0, "first");'
        if source.count(anchor) != 10:
            raise ValueError('Market variant requires all ten source guards')
        return source.replace(anchor, 'require(0 != flag, "first");')
    if variant == 'collision':
        anchor = 'require(flag != 0, "first");'
        if source.count(anchor) != 10:
            raise ValueError('Market collision variant requires ten source guards')
        return source.replace(anchor,
            'uint256 _verity_slice_tmp_0_memory = flag; '
            'require(_verity_slice_tmp_0_memory != 0, "first");')
    if variant == 'bindings':
        anchors = [('market.midnight', 'address'), ('market.maturity', 'uint256'),
                   ('market.collateralParams[0].token', 'address'),
                   ('market.collateralParams[1].token', 'address')]
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
def stateful_constants_sources(original, constants, variant):
    """Equivalent constant programs: returns the contract and its constants file."""
    if variant == 'baseline':
        return original, constants
    if variant == 'folded':
        # Every compile-time spelling replaced by its plain decimal value.
        folds = [
            ('constants', '= 1e18;', '= 1000000000000000000;'),
            ('constants', '= 0.000014e18;', '= 14000000000000;'),
            ('constants', '= 1_000_000;', '= 1000000;'),
            ('constants', 'uint256(0.01e18) / uint256(365 days)', 'uint256(10000000000000000) / uint256(31536000)'),
            ('constants', '= 2 hours + 30 minutes;', '= 9000;'),
            ('constants', '= 0xff_ff;', '= 65535;'),
            ('constants', '= 2 ** 255 + (7 - 3) * 10 ** 3 / 8;',
             '= 57896044618658097711785492504343953926634992332820282019728792003956564820468;'),
            ('original', '7 weeks - 1 ether / 1e18', '4233599'),
            ('original', '+ 1 days;', '+ 86400;'),
        ]
        texts = {'constants': constants, 'original': original}
        for key, before, after in folds:
            if texts[key].count(before) != 1:
                raise ValueError(f'missing constants source anchor: {before}')
            texts[key] = texts[key].replace(before, after)
        return texts['original'], texts['constants']
    if variant == 'contract-scoped':
        # File-level constants become contract constants in a single file.
        declarations = [line for line in constants.splitlines() if ' constant ' in line]
        import_line = next(line for line in original.splitlines() if line.startswith('import '))
        anchor = 'contract SequenceFixture {\n'
        if original.count(anchor) != 1:
            raise ValueError('missing constants contract anchor')
        scoped = original.replace(import_line + '\n', '').replace(
            anchor, anchor + ''.join(f'    {line}\n' for line in declarations))
        return scoped, 'pragma solidity 0.8.34;\n'
    raise ValueError(variant)


def stateful_arithmetic_source(original, variant):
    """Compound assignments and `%` spelled out as plain checked arithmetic."""
    if variant == 'baseline':
        return original
    replacements = {
        'expanded': {
            'total += low + 10;': 'total = total + (low + 10);',
            'credit[msg.sender] += low % 7 + 1;': 'credit[msg.sender] = credit[msg.sender] + (low % 7 + 1);',
            'shares[low % 3][msg.sender] += low;': 'shares[low % 3][msg.sender] = shares[low % 3][msg.sender] + low;',
            'shares[low % 3][msg.sender] *= 3;': 'shares[low % 3][msg.sender] = shares[low % 3][msg.sender] * 3;',
            'shares[low % 3][msg.sender] -= 4;': 'shares[low % 3][msg.sender] = shares[low % 3][msg.sender] - 4;',
            'total /= low % 4 + 1;': 'total = total / (low % 4 + 1);',
            'total %= 1000;': 'total = total % 1000;',
            'ticks += 50;': 'ticks = ticks + 50;',
            'ticks--;': 'ticks = ticks - 1;',
            'last++;': 'last = last + 1;',
            # Keep solc's order: the divisor is evaluated before the key.
            'shares[total - last - 4][msg.sender] -= 100 / (total % 4);':
            'uint256 cut = 100 / (total % 4);\n'
            '        shares[total - last - 4][msg.sender] = shares[total - last - 4][msg.sender] - cut;',
            'ticks -= 1;': 'ticks = ticks - 1;',
            '--last;': 'last = last - 1;',
            'total %= last;': 'total = total % last;',
        },
        'division': {
            'uint256 low = value % 1000;': 'uint256 low = value - value / 1000 * 1000;',
            'total %= 1000;': 'total = total - total / 1000 * 1000;',
            'return (total % 97, value % (last + 1));':
            'return (total - total / 97 * 97, value - value / (last + 1) * (last + 1));',
            'total %= last;': 'total = total - total / last * last;',
            'return (credit[msg.sender] % 1000, shares[1][msg.sender], ticks);':
            'return (credit[msg.sender] - credit[msg.sender] / 1000 * 1000, shares[1][msg.sender], ticks);',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if original.count(before) != 1:
            raise ValueError(f'missing arithmetic source anchor: {before}')
        original = original.replace(before, after)
    return original


def stateful_member_write_source(original, variant):
    """Struct member writes through aliases, direct paths, or expanded compounds."""
    if variant == 'baseline':
        return original
    replacements = {
        'direct': {
            '        State storage s = states[id];\n': '',
            's.spacing = uint8(value % 200);': 'states[id].spacing = uint8(value % 200);',
            's.fee0 = uint16(value % 1000);': 'states[id].fee0 = uint16(value % 1000);',
            's.fee1 += 3;': 'states[id].fee1 += 3;',
            's.fee1++;': 'states[id].fee1++;',
            '        State storage p = positions[id][msg.sender];\n': '',
            'p.credit = uint128(value % 1000) + p.credit;':
            'positions[id][msg.sender].credit = uint128(value % 1000) + positions[id][msg.sender].credit;',
            'return (s.spacing + s.fee0, p.credit);':
            'return (states[id].spacing + states[id].fee0, positions[id][msg.sender].credit);',
        },
        'expanded': {
            's.fee1 += 3;': 's.fee1 = s.fee1 + 3;',
            's.fee1++;': 's.fee1 = s.fee1 + 1;',
            'states[id].units += uint128(value % 1000000);':
            'states[id].units = states[id].units + uint128(value % 1000000);',
            'positions[id][msg.sender].wide += value % 1000 + 1;':
            'positions[id][msg.sender].wide = positions[id][msg.sender].wide + (value % 1000 + 1);',
            # Keep solc's order: the divisor is evaluated before the key.
            'states[bytes32(total - 9)].wide -= 100 / (total % 4);':
            'uint256 cut = 100 / (total % 4);\n'
            '        states[bytes32(total - 9)].wide = states[bytes32(total - 9)].wide - cut;',
            's.wide -= total;': 's.wide = s.wide - total;',
            's.fee0 /= uint16(total % 3);': 's.fee0 = s.fee0 / uint16(total % 3);',
            'delete positions[bytes32(total % 4)][msg.sender].credit;':
            'positions[bytes32(total % 4)][msg.sender].credit = 0;',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if original.count(before) != 1:
            raise ValueError(f'missing member-write source anchor: {before}')
        original = original.replace(before, after)
    return original


def stateful_loop_source(original, variant):
    """Counted loops and reassigned locals in equivalent spellings."""
    if variant == 'baseline':
        return original
    replacements = {
        'prefix': {
            'for (uint256 i = 0; i < n; i++) {': 'for (uint256 i; i < n; ++i) {',
            'for (uint256 j; j < 3; ++j) {': 'for (uint256 j = 0; j < 3; j += 1) {',
            'for (uint256 i = 0; i < 4; i += 1) {': 'for (uint256 i; i < 4; i++) {',
            'for (uint256 i = 0; i < 6; i++) {': 'for (uint256 i = 0; i < 6; ++i) {',
        },
        'expanded': {
            'uint256 acc;\n': 'uint256 acc = 0;\n',
            'acc += i * 3 + 1;': 'acc = acc + (i * 3 + 1);',
            'total += j;': 'total = total + j;',
            'key += 1;': 'key = key + 1;',
            'k -= n / 2;': 'k = k - n / 2;',
            'acc -= i;': 'acc = acc - i;',
            'uint256 sum;': 'uint256 sum = 0;',
            'sum += slots[i]': 'sum = sum + slots[i]',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if original.count(before) != 1:
            raise ValueError(f'missing loop source anchor: {before}')
        original = original.replace(before, after)
    return original


def stateful_unchecked_source(original, variant):
    """Wrapping arithmetic in split blocks or explicit assignments."""
    if variant == 'baseline':
        return original
    replacements = {
        'split': {
            '            total += value;\n': '            total += value;\n        }\n        unchecked {\n',
            '            wrapped = value * 3 - 10;\n': '            wrapped = value * 3 - 10;\n        }\n        unchecked {\n',
        },
        'explicit': {
            'total += value;': 'total = total + value;',
            'small += uint8(value % 256) + 250;': 'small = small + (uint8(value % 256) + 250);',
            'mid -= uint64(value % 5) + 1;': 'mid = mid - (uint64(value % 5) + 1);',
            'credit[msg.sender]--;': 'credit[msg.sender] -= 1;',
            'return x - 10 + 3;': 'uint256 y = x - 10;\n            return y + 3;',
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if original.count(before) != 1:
            raise ValueError(f'missing unchecked source anchor: {before}')
        original = original.replace(before, after)
    return original


def stateful_tuple_source(original, variant):
    """Tuple declarations and returns spelled as scalar locals and branches."""
    if variant == 'baseline':
        return original
    replacements = {
        'expanded': {
            '(uint128 a, , uint128 c) = split(value);': '(uint128 a, uint128 unused, uint128 c) = split(value);',
            """        (uint256 start, uint256 end, uint256 lo, uint256 hi) =
            t < 1 days ? (0 days, 1 days, uint256(a) * 3, uint256(c)) :
            t < 7 days ? (1 days, 7 days, uint256(c), uint256(a) + 5) :
                         (7 days, 8 days, a, c);
""": """        uint256 start;
        uint256 end;
        uint256 lo;
        uint256 hi;
        if (t < 1 days) {
            end = 1 days;
            lo = uint256(a) * 3;
            hi = c;
        } else if (t < 7 days) {
            start = 1 days;
            end = 7 days;
            lo = c;
            hi = uint256(a) + (t - 1 days);
        } else {
            start = 7 days;
            end = 8 days;
            lo = a;
            hi = c;
        }
""",
        },
        'inline': {
            '(uint256 p, uint256 q) = pair(value % 1000);': '(uint256 p, uint256 q) = (value % 1000, value % 1000 + 1);',
            '        return triple(total);\n': """        if (total % 2 == 0) return (total, m[0], m[1]);
        return (m[2], total + 1, m[3]);
""",
        },
    }
    if variant not in replacements:
        raise ValueError(variant)
    for before, after in replacements[variant].items():
        if original.count(before) != 1:
            raise ValueError(f'missing tuple source anchor: {before}')
        original = original.replace(before, after)
    return original
