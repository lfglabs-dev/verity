"""Located near-miss rejections and positive controls for Yul `mstore(x, n)` array length shrinks.

Admits only `assembly { mstore(x, n) }` (or `assembly ("memory-safe") { mstore(x, n) }`) where `x`
is an unaliased local `T[] memory` variable (`T` a static value type, not a parameter) holding a
`new T[](cap)` allocation and `n <= cap` is proved on every path reaching the block. Each case is
imported in its own directory under `.lake/` with `timeout=900`: positive controls must elaborate,
have `denoteCovered == true`, compile through `CompilationModel.compile`, and leave an `.olean`;
rejections must fail with the exact `Fixture.sol:line:column: <NodeType>: [solidity-import:unsupported]`
diagnostic and leave no `.olean`.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'unproved': 'Yul memory array length mstore requires a length provably at most the allocated array length',
    'param-array': 'Yul memory array length mstore requires a local memory array variable, not a parameter',
    'unaliased': 'Yul memory array length mstore requires an unaliased local new-array allocation',
    'scalar-len': 'Yul memory array length mstore requires a scalar local, parameter, constant or literal length',
    'uint-len': 'Yul memory array length mstore requires an unsigned integer length',
    'shadowed-len': 'Yul memory array length mstore length identifier is shadowed',
    'fixed-mstore': 'Yul mstore requires a fixed address below 0x80',
    'unbound-xs': 'unbound Yul identifier xs',
    'unbound-b': 'unbound Yul identifier b',
    'unbound-fixed': 'unbound Yul identifier fixedArr',
    'unbound-other': 'unsupported Yul expression statement pop (unsupported statement InlineAssembly)',
}

# (case_name, params_sig, call_sig_types, ret_decl, body_statements, expected)
# expected is None for positive controls, or (marker, occurrence, construct, message_key)
CASES = [
    # --- Positive controls ---
    ('pos-literal-zero', 'uint256 cap', 'uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        assembly { mstore(xs, 0) }',
     None),
    ('pos-literal-partial', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](5);\n        xs[0] = 11;\n        xs[1] = 22;\n'
     '        assembly ("memory-safe") { mstore(xs, 2) }',
     None),
    ('pos-no-shrink-reflexive', 'uint256 cap', 'uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        assembly { mstore(xs, cap) }',
     None),
    ('pos-require-le', 'uint256 cap, uint256 n', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'require(n <= cap, "bound");\n        xs = new uint256[](cap);\n'
     '        assembly { mstore(xs, n) }',
     None),
    ('pos-if-revert-guard', 'uint256 cap, uint256 n', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'if (n > cap) { revert(); }\n        xs = new uint256[](cap);\n'
     '        assembly { mstore(xs, n) }',
     None),
    ('pos-while-paginated', 'bool go, uint256 pageSize', 'bool,uint256', 'returns (address[] memory page)',
     'page = new address[](pageSize);\n        uint256 count = 0;\n'
     '        while (go && count < pageSize) {\n            page[count] = address(0x2);\n'
     '            count++;\n            go = false;\n        }\n'
     '        assembly { mstore(page, count) }',
     None),
    ('pos-for-filtered', 'uint256 a, uint256 b', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](2);\n        uint256 kept = 0;\n'
     '        for (uint256 i = 0; i < 2; i++) {\n'
     '            uint256 v = i == 0 ? a : b;\n'
     '            if (v > 0) { xs[kept] = v; kept++; }\n        }\n'
     '        assembly { mstore(xs, kept) }',
     None),
    ('pos-checked-sub', 'uint256 cap, uint256 drop', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 keep = cap - drop;\n'
     '        assembly { mstore(xs, keep) }',
     None),
    ('pos-min-ternary', 'uint256 cap, uint256 want', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 keep = want < cap ? want : cap;\n'
     '        assembly { mstore(xs, keep) }',
     None),

    # --- 1. Grow rejections ---
    ('rej-grow-literal', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        assembly { mstore(xs, 5) }',
     ('5)', 0, 'YulLiteral', 'unproved')),
    ('rej-grow-const-var', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        uint256 big = 4;\n        assembly { mstore(xs, big) }',
     ('big)', 0, 'YulIdentifier', 'unproved')),
    ('rej-grow-inclusive-while', 'uint256 cap', 'uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 count = 0;\n'
     '        while (count <= cap) {\n            count++;\n        }\n'
     '        assembly { mstore(xs, count) }',
     ('count)', 0, 'YulIdentifier', 'unproved')),
    ('rej-grow-second-shrink', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        assembly { mstore(xs, 2) }\n'
     '        assembly { mstore(xs, 3) }',
     ('3)', 0, 'YulLiteral', 'unproved')),

    # --- 2. Non-array target rejections ---
    ('rej-non-array-scalar', '', '', 'returns (uint256 p)',
     'p = 0x80;\n        assembly { mstore(p, 0) }',
     ('mstore(p, 0)', 0, 'YulFunctionCall', 'fixed-mstore')),
    ('rej-non-array-bytes', '', '', 'returns (bytes memory b)',
     'b = abi.encode(uint256(1));\n        assembly { mstore(b, 0) }',
     ('b, 0)', 0, 'YulIdentifier', 'unbound-b')),
    ('rej-non-array-fixed', '', '', 'returns (uint256)',
     'uint256[2] memory fixedArr;\n        assembly { mstore(fixedArr, 1) }\n'
     '        return fixedArr[0];',
     ('fixedArr, 1)', 0, 'YulIdentifier', 'unbound-fixed')),

    # --- 3. Offset target & non-exact block rejections ---
    ('rej-offset-element-slot', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        assembly { mstore(add(xs, 0x20), 0) }',
     ('xs, 0x20)', 0, 'YulIdentifier', 'unbound-xs')),
    ('rej-offset-literal-heap', '', '', 'returns (uint256)',
     'assembly { mstore(0x80, 0) }\n        return 1;',
     ('mstore(0x80, 0)', 0, 'YulFunctionCall', 'fixed-mstore')),
    ('rej-two-stmt-assembly', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        assembly { mstore(xs, 0) mstore(0x00, 1) }',
     ('xs, 0)', 0, 'YulIdentifier', 'unbound-xs')),
    ('rej-other-opcode-pop', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        assembly { pop(0) }',
     ('pop(0)', 0, 'YulExpressionStatement', 'unbound-other')),

    # --- 4. Unprovable `n` & aliasing/parameter rejections ---
    ('rej-unproved-param', 'uint256 cap, uint256 n', 'uint256,uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        assembly { mstore(xs, n) }',
     ('n)', 1, 'YulIdentifier', 'unproved')),
    ('rej-unproved-short-circuit-init', 'bool keepGoing, uint256 cap', 'bool,uint256',
     'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 count = 5;\n'
     '        while (keepGoing && count < cap) {\n            count++;\n        }\n'
     '        assembly { mstore(xs, count) }',
     ('count)', 0, 'YulIdentifier', 'unproved')),
    ('rej-unproved-post-loop-inc', 'bool keepGoing, uint256 cap', 'bool,uint256',
     'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 count = 0;\n'
     '        while (keepGoing && count < cap) {\n            count++;\n            keepGoing = false;\n'
     '        }\n        count++;\n        assembly { mstore(xs, count) }',
     ('count)', 0, 'YulIdentifier', 'unproved')),
    ('rej-unproved-unchecked-sub', 'uint256 cap, uint256 drop', 'uint256,uint256',
     'returns (uint256[] memory xs)',
     'xs = new uint256[](cap);\n        uint256 keep;\n'
     '        unchecked { keep = cap - drop; }\n        assembly { mstore(xs, keep) }',
     ('keep)', 0, 'YulIdentifier', 'unproved')),
    ('rej-unproved-dirty-narrow-yul', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint8 n;\n        assembly { n := 0x0102 }\n'
     '        if (n <= 4) {\n            assembly { mstore(xs, n) }\n        }',
     ('n)', 0, 'YulIdentifier', 'unproved')),
    ('rej-compound-yul-len', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        assembly { mstore(xs, add(1, 1)) }',
     ('add(1, 1)', 0, 'YulFunctionCall', 'scalar-len')),
    ('rej-signed-len-local', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        int256 s = 1;\n        assembly { mstore(xs, s) }',
     ('s)', 1, 'YulIdentifier', 'uint-len')),
    ('rej-parameter-array', 'uint256[] memory xs', '«uint256[]»', 'returns (uint256)',
     'assembly { mstore(xs, 0) }\n        return xs.length;',
     ('xs, 0)', 0, 'YulIdentifier', 'param-array')),
    ('rej-aliased-array', '', '', 'returns (uint256)',
     'uint256[] memory xs = new uint256[](3);\n        uint256[] memory aliasView;\n'
     '        aliasView = xs;\n        assembly { mstore(xs, 1) }\n        return aliasView.length;',
     ('xs, 1)', 0, 'YulIdentifier', 'unaliased')),
    ('rej-shrink-inside-loop', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](3);\n        for (uint256 i = 0; i < 2; i++) {\n'
     '            assembly { mstore(xs, 1) }\n        }',
     ('xs, 1)', 0, 'YulIdentifier', 'unaliased')),
    ('pos-helper-always-revert', 'uint256 cap, uint256 n', 'uint256,uint256',
     'returns (uint256[] memory xs)',
     'if (n > cap) { _alwaysRevert(); }\n        xs = new uint256[](cap);\n'
     '        assembly { mstore(xs, n) }',
     None),
    ('pos-clean-narrow-literal-copy', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint8 a = 2;\n        uint16 b = a;\n'
     '        assembly { mstore(xs, b) }',
     None),
    ('rej-helper-return-not-revert', 'uint256 cap, uint256 n', 'uint256,uint256',
     'returns (uint256[] memory xs)',
     'if (n > cap) { _noop(); }\n        xs = new uint256[](cap);\n'
     '        assembly { mstore(xs, n) }',
     ('n)', 1, 'YulIdentifier', 'unproved')),
    ('rej-narrow-cast-len', 'uint256 x', 'uint256', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint8 n = uint8(x);\n        require(n <= 4);\n'
     '        assembly { mstore(xs, n) }',
     ('n)', 0, 'YulIdentifier', 'unproved')),
    ('rej-dirty-helper-narrow-len', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint8 n = _dirtyNarrow();\n        require(n <= 4);\n'
     '        assembly { mstore(xs, n) }',
     ('n)', 0, 'YulIdentifier', 'unproved')),
    ('rej-copy-dirty-yul-narrow', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint8 raw;\n        assembly { raw := 0x0102 }\n'
     '        uint8 m = raw;\n        require(m <= 4);\n        assembly { mstore(xs, m) }',
     ('m)', 0, 'YulIdentifier', 'unproved')),
    ('rej-rebound-aliased-array-len', 'uint256 n', 'uint256', 'returns (uint256[] memory xs)',
     'uint256[] memory a = new uint256[](10);\n        uint256[] memory aliasA;\n'
     '        aliasA = a;\n        require(n <= a.length);\n        a = new uint256[](2);\n'
     '        aliasA = a;\n        xs = new uint256[](a.length);\n'
     '        assembly { mstore(xs, n) }',
     ('n)', 1, 'YulIdentifier', 'unproved')),
    ('rej-signed-const-len', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        assembly { mstore(xs, SCONST) }',
     ('SCONST)', 0, 'YulIdentifier', 'uint-len')),
    ('rej-array-as-len', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint256[] memory ys = new uint256[](2);\n'
     '        assembly { mstore(xs, ys) }',
     ('ys)', 0, 'YulIdentifier', 'scalar-len')),
    ('pos-caller-param-collides-const', 'uint256 TWO', 'uint256',
     'returns (uint256[] memory)',
     'if (TWO == 999) { return new uint256[](0); }\n        return _midConst(1);',
     None),
    ('pos-folded-const-shrink', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        assembly { mstore(xs, TWO) }',
     None),
    ('rej-caller-param-shadows-const-grow', '', '', 'returns (uint256[] memory)',
     'return _midGrowConst(1);',
     ('BIG_K)', 0, 'YulIdentifier', 'unproved')),
    ('rej-caller-param-shadows-target-grow', '', '', 'returns (uint256[] memory)',
     'return _midTarget(0);',
     ('7)', 0, 'YulLiteral', 'unproved')),
    ('rej-folded-const-seq-shrink', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        assembly { mstore(xs, TWO) }\n'
     '        assembly { mstore(xs, 3) }',
     ('3)', 0, 'YulLiteral', 'unproved')),
    ('rej-udvt-uint0256-custom-le', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](1);\n        uint0256 udvtBad;\n        uint0256 z;\n'
     '        if (udvtBad <= z) {\n            assembly { mstore(xs, udvtBad) }\n        }',
     ('udvtBad)', 0, 'YulIdentifier', 'uint-len')),
    ('rej-udvt-uint9-signed', '', '', 'returns (uint256[] memory xs)',
     'xs = new uint256[](4);\n        uint9 udvtSigned;\n'
     '        assembly { mstore(xs, udvtSigned) }',
     ('udvtSigned)', 0, 'YulIdentifier', 'uint-len')),
]


def render_source(params_sig, ret_decl, statements):
    ret_part = f' {ret_decl}' if ret_decl else ''
    return (
        '// SPDX-License-Identifier: MIT\n'
        'pragma solidity 0.8.34;\n\n'
        'type uint0256 is uint8;\n'
        'type uint9 is int256;\n'
        'function _alwaysLeUdvt(uint0256, uint0256) pure returns (bool) { return true; }\n'
        'using { _alwaysLeUdvt as <= } for uint0256 global;\n\n'
        'contract C {\n'
        '    int256 internal constant SCONST = 1;\n'
        '    uint256 internal constant TWO = 1 + 1;\n'
        '    uint256 internal constant BIG_K = 5;\n'
        '    function _noop() internal pure { return; }\n'
        '    function _alwaysRevert() internal pure { revert(); }\n'
        '    function _dirtyNarrow() internal pure returns (uint8 r) { assembly { r := 0x0102 } }\n'
        '    function _leafConst() internal pure returns (uint256[] memory) {\n'
        '        uint256[] memory xs = new uint256[](4);\n'
        '        assembly { mstore(xs, TWO) }\n'
        '        return xs;\n'
        '    }\n'
        '    function _midConst(uint256 TWO) internal pure returns (uint256[] memory) {\n'
        '        if (TWO == 0) { return new uint256[](0); }\n'
        '        return _leafConst();\n'
        '    }\n'
        '    function _leafGrowConst() internal pure returns (uint256[] memory) {\n'
        '        uint256[] memory xs = new uint256[](2);\n'
        '        assembly { mstore(xs, BIG_K) }\n'
        '        return xs;\n'
        '    }\n'
        '    function _midGrowConst(uint256 BIG_K) internal pure returns (uint256[] memory) {\n'
        '        if (BIG_K == 0) { return new uint256[](0); }\n'
        '        return _leafGrowConst();\n'
        '    }\n'
        '    function _leafTargetGrow() internal pure returns (uint256[] memory) {\n'
        '        uint256[] memory arrTarget = new uint256[](2);\n'
        '        assembly { mstore(arrTarget, 7) }\n'
        '        return arrTarget;\n'
        '    }\n'
        '    function _midTarget(uint256 arrTarget) internal pure returns (uint256[] memory) {\n'
        '        if (arrTarget == 999) { return new uint256[](0); }\n'
        '        return _leafTargetGrow();\n'
        '    }\n'
        f'    function checked({params_sig}) external pure{ret_part} {{\n'
        f'        {statements}\n'
        '    }\n'
        '}\n'
    )


def location(text, marker, occurrence):
    start = -1
    for _ in range(occurrence + 1):
        start = text.index(marker, start + 1)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    lake_dir = root / '.lake'
    lake_dir.mkdir(parents=True, exist_ok=True)
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='yul-array-length-shrink-rejections-', dir=lake_dir)))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, params_sig, call_sig_types, ret_decl, statements, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = render_source(params_sig, ret_decl, statements)
        (directory / 'Fixture.sol').write_text(text)
        compile_guard = 'import Compiler.Codegen\n' if expected is None else ''
        compile_checks = (
            '#guard tested.report.functions.all (·.denoteCovered)\n'
            '#guard (Compiler.CompilationModel.compile tested.model [0x1] .osaka).isOk\n'
            if expected is None else ''
        )
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
{compile_guard}solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
  function checked({call_sig_types})
{compile_checks}''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(
            ['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
            cwd=root, text=True, capture_output=True, timeout=900,
        )
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if expected is None:
            if result.returncode or not artifact.exists():
                raise SystemExit(f'{name}: positive control failed\n{log}')
            diagnostic = None
        else:
            marker, occurrence, construct, key = expected
            line, column = location(text, marker, occurrence)
            diagnostic = (
                f'Fixture.sol:{line}:{column}: {construct}: '
                f'[solidity-import:unsupported] {MESSAGES[key]}'
            )
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({
            'case': name,
            'diagnostic': diagnostic,
            'sourceSha256': hashlib.sha256(text.encode()).hexdigest(),
        })
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass yul-array-length-shrink-{name}', flush=True)
    print(f'yul array length shrink rejections passed ({len(results)} cases): {output}')


if __name__ == '__main__':
    main()
