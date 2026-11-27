"""Located rejections and acceptances for linked library calls under
`linkedLibrariesMatchSource := true` (#2728).

With the trust assumption on, a direct `L.f(...)` DELEGATECALL inlines `f`'s body only when
the arguments are value types, storage references or `bytes memory` (explicitly copied in),
the results are value types or `bytes memory` (explicitly copied out), and nothing the body
reaches (internal helpers, operators and modifiers, transitively) depends on the DELEGATECALL
frame. Each case below must reject at the stated token with the stated diagnostic, or import.
Without the flag the same calls keep the `check_library_call_rejections` diagnostic.

`--mutant frame-check`, `returndata-check`, `alias-copy-in` or `drop-copy-out` builds a
snapshot with that guard or copy disabled, requires the targeted cases to elaborate there,
then this suite to fail on that snapshot.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json

PRAGMA = ('pragma solidity 0.8.34;\n'
          'interface I { function g(uint256) external view returns (uint256); }\n')
UDVT_OPERATOR = (
    'type TaggedWord is uint256;\n'
    'function addTaggedWithSig(TaggedWord x, TaggedWord y) pure returns (TaggedWord) {\n'
    '    return TaggedWord.wrap(TaggedWord.unwrap(x) + TaggedWord.unwrap(y) + uint32(msg.sig));\n'
    '}\n'
    'using {addTaggedWithSig as +} for TaggedWord global;\n')
SHADOW_UDVT_PREAMBLE = (
    'import "./A_Shadow.sol" as AShadow;\n'
    'import "./Z_Shadow.sol" as ZShadow;\n'
    'type HomonymVal is uint8;\n')
PROFILE = ('{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, '
           'bytecodeHash := "none"{extra} }')
CONTRACT = ('contract C {\n'
            '    uint256 public root;\n'
            '    S.Cell internal cell;\n'
            '    mapping(uint256 => uint256) internal m;\n'
            '    function f(uint256 a, uint256 b) external {\n'
            '        {body}\n'
            '    }\n'
            '{members}'
            '}\n')
STRUCT = '    struct Cell { uint256 v; }\n'

# name, library body, contract body, extra contract members, token, diagnostic (None: imports)
CASES = [
    ('value-and-storage-args',
     '    function h(Cell storage c, uint256 a) external returns (uint256) { c.v = a; return a + 1; }\n',
     'uint256 r = S.h(cell, a);\n        root = r + b;', '', None, None),
    ('stateful-binary-operand',
     '    function h(Cell storage c, uint256 a) external returns (uint256) { c.v = a; return a + 1; }\n',
     'root = S.h(cell, a) + b;', '', 'S.h(cell, a) + b',
     'stateful helper operands require explicit evaluation-order support'),
    ('void-public-call',
     '    function h(Cell storage c, uint256 a) public { c.v = a; }\n',
     'S.h(cell, a);\n        root = b;', '', None, None),
    ('void-external-call',
     '    function h(Cell storage c, uint256 a) external { c.v = a; }\n',
     'S.h(cell, a);\n        root = b;', '', None, None),
    ('multi-return-external-call',
     '    function h(uint256 a, uint256 b) external pure returns (uint256, uint256) { return (a + 1, b + 2); }\n',
     '(uint256 x, uint256 y) = S.h(a, b);\n        root = x + y;', '', None, None),
    ('homonymous-file-udvt-clean',
     '    function h(HomonymVal v) external pure returns (HomonymVal) { return v; }\n',
     'HomonymVal v = HomonymVal.wrap(0);\n        assembly { v := a }\n'
     '        HomonymVal r = S.h(v);\n        uint256 out;\n        assembly { out := r }\n'
     '        root = out + b;', '', None, None),
    ('immutable-initializer',
     '    function h(uint256 a) external pure returns (uint256) { return a + 1; }\n',
     'root = IMM + a;', '    uint256 internal immutable IMM = S.h(1);\n', 'IMM + a',
     'immutable state variable IMM is outside this slice'),
    ('internal-call-unchanged',
     '    function h(uint256 a, uint256 b) internal pure returns (uint256) { return a ^ b; }\n',
     'root = S.h(a, b);', '', None, None),
    ('flag-off',
     '    function h(uint256 a, uint256 b) external pure returns (uint256) { return a ^ b; }\n',
     'root = S.h(a, b);', '', 'S.h(a, b)', 'external library calls are outside this slice'),
    ('flag-off-interface-call-in-body',
     '    function h(uint256 a) external view returns (uint256) { return I(address(uint160(a))).g(a); }\n',
     'm[b + 1] = S.h(a);', '', 'S.h', 'external library calls are outside this slice'),
    ('interface-call-in-body-computed-key',
     '    function h(uint256 a) external view returns (uint256) { return I(address(uint160(a))).g(a); }\n',
     'm[b + 1] = S.h(a);', '', 'S.h',
     'solc evaluates the right-hand side first'),
    ('returndatasize-after-call',
     '    function h(uint256 a) external pure returns (uint256) { return a + 1; }\n',
     'uint256 r = S.h(a);\n        uint256 z;\n        assembly { z := returndatasize() }\n'
     '        root = r + z + b;', '', 'returndatasize',
     'Yul returndatasize in a function that makes a linked library call'),
    ('returndatasize-before-call',
     '    function h(uint256 a) external pure returns (uint256) { return a + 1; }\n',
     'uint256 z;\n        assembly { z := returndatasize() }\n        uint256 r = S.h(a);\n'
     '        root = r + z + b;', '', 'S.h',
     'linked library calls in a function that reads Yul returndatasize'),
    ('bubbled-revert-after-call',
     '    function h(uint256 a) external pure returns (uint256) { return a + 1; }\n',
     'uint256 r = S.h(a);\n        root = r + b;\n        assembly {\n'
     '            let p := mload(0x40)\n            returndatacopy(p, 0, returndatasize())\n'
     '            revert(p, returndatasize())\n        }', '', 'returndatacopy',
     'Yul returndatasize in a function that makes a linked library call'),
    ('bubbled-revert-before-call',
     '    function h(uint256 a) external pure returns (uint256) { return a + 1; }\n',
     'if (b == 1) {\n            assembly {\n                let p := mload(0x40)\n'
     '                returndatacopy(p, 0, returndatasize())\n'
     '                revert(p, returndatasize())\n            }\n        }\n'
     '        root = S.h(a);', '', 'S.h',
     'linked library calls in a function that reads Yul returndatasize'),
    ('using-for',
     '    function h(uint256 a, uint256 b) public pure returns (uint256) { return a ^ b; }\n',
     'root = a.h(b);', '    using S for uint256;\n', 'a.h(b)',
     'attached linked library calls (using L for T) are outside this slice'),
    ('memory-argument',
     '    function h(bytes memory data) external pure returns (uint256) { return data.length; }\n',
     'root = S.h(abi.encode(a, b));', '', None, None),
    ('memory-result',
     '    function h(uint256 a) external pure returns (bytes memory) { return abi.encode(a); }\n',
     'root = S.h(a).length;', '', None, None),
    ('bytes-copy-in-isolation',
     '    function h(bytes memory data) external pure returns (bytes memory out) {\n'
     '        bytes memory cp = new bytes(data.length + 1);\n'
     '        for (uint256 i = 0; i < data.length; ++i) { cp[i] = data[i]; }\n'
     '        if (data.length > 0) { data[0] = hex"ff"; }\n'
     '        cp[data.length] = hex"77";\n'
     '        out = cp;\n'
     '    }\n',
     'bytes memory orig = new bytes(1 + 1);\n'
     '        orig[0] = bytes1(uint8(a));\n'
     '        orig[1] = bytes1(uint8(b));\n'
     '        bytes memory ret = S.h(orig);\n'
     '        ret[0] = hex"aa";\n'
     '        root = (uint256(uint8(orig[0])) << 16) | (uint256(uint8(ret[0])) << 8) | uint256(uint8(ret[2]));',
     '', None, None),
    ('bytes-copy-out-disjoint',
     '    function h(uint8 v) external pure returns (bytes memory x, bytes memory y) {\n'
     '        bytes memory shared = new bytes(1 + 1);\n'
     '        shared[0] = bytes1(v);\n'
     '        shared[1] = hex"55";\n'
     '        return (shared, shared);\n'
     '    }\n',
     '(bytes memory x, bytes memory y) = S.h(uint8(a));\n'
     '        x[0] = bytes1(uint8(b));\n'
     '        root = (uint256(uint8(x[0])) << 8) | uint256(uint8(y[0]));',
     '', None, None),
    ('flag-off-bytes-argument',
     '    function h(bytes memory data) external pure returns (uint256) { return data.length; }\n',
     'root = S.h(abi.encode(a, b));', '', 'S.h',
     'external library calls are outside this slice'),
    ('flag-off-bytes-result',
     '    function h(uint256 a) external pure returns (bytes memory) { return abi.encode(a); }\n',
     'root = S.h(a).length;', '', 'S.h',
     'external library calls are outside this slice'),
    ('bytes-calldata-argument',
     '    function h(bytes calldata data) external pure returns (uint256) { return data.length; }\n',
     'root = S.h(msg.data);', '', 'bytes calldata data',
     'linked library call parameters must be value types or storage references'),
    ('string-memory-argument',
     '    function h(string memory s) external pure returns (uint256) { return bytes(s).length; }\n',
     'root = S.h("hi");', '', 'string memory s',
     'linked library call parameters must be value types or storage references'),
    ('string-memory-result',
     '    function h(uint256) external pure returns (string memory) { return "hi"; }\n',
     'root = bytes(S.h(a)).length;', '', 'string memory)',
     'linked library call results must be value types'),
    ('uint-array-memory-argument',
     '    function h(uint256[] memory xs) external pure returns (uint256) { return xs.length; }\n',
     'uint256[] memory xs = new uint256[](1); xs[0] = a; root = S.h(xs);', '', 'uint256[] memory xs',
     'linked library call parameters must be value types or storage references'),
    ('uint-array-memory-result',
     '    function h(uint256 a) external pure returns (uint256[] memory) {\n'
     '        uint256[] memory xs = new uint256[](1); xs[0] = a; return xs;\n'
     '    }\n',
     'uint256[] memory xs = S.h(a); root = xs.length + b;', '', 'uint256[] memory)',
     'linked library call results must be value types'),
    ('struct-memory-argument',
     '    function h(Cell memory c) external pure returns (uint256) { return c.v; }\n',
     'root = S.h(S.Cell(a));', '', 'Cell memory c',
     'linked library call parameters must be value types or storage references'),
    ('struct-memory-result',
     '    function h(uint256 a) external pure returns (Cell memory) { return Cell(a); }\n',
     'S.Cell memory c = S.h(a); root = c.v + b;', '', 'Cell memory)',
     'linked library call results must be value types'),
    ('storage-ref-result',
     '    function h(Cell storage c) external pure returns (Cell storage) { return c; }\n',
     'S.Cell storage c = S.h(cell); root = c.v + a + b;', '', 'Cell storage)',
     'linked library call results must be value types'),
    ('short-string-bytes-argument',
     '    function h(bytes memory data) external pure returns (uint256) { return data.length; }\n',
     'root = S.h(bytes(_short(bytes32(a)))) + b;',
     '    function _short(bytes32 s) internal pure returns (string memory) {\n'
     '        string memory str = new string(32);\n'
     '        assembly ("memory-safe") {\n'
     '            mstore(str, 4)\n'
     '            mstore(add(str, 0x20), s)\n'
     '        }\n'
     '        return str;\n'
     '    }\n',
     'bytes(_short(bytes32(a)))',
     'ShortStrings assembly-allocated buffer passed to or returned from a linked library call is outside this slice'),
    ('yul-mload-linked-bytes-return',
     '    function h(uint256 a) external pure returns (bytes memory) {\n'
     '        return a == 0 ? bytes("") : abi.encode(a);\n'
     '    }\n',
     'bytes memory ret = S.h(a);\n'
     '        uint256 w;\n'
     '        assembly { w := mload(add(ret, 0x20)) }\n'
     '        root = w + b;', '', 'mload(add(ret, 0x20))',
     'Yul word load from linked library bytes return is outside this slice'),
    ('short-string-byte-index-loop',
     '    function h(uint256 a) external pure returns (bytes memory) { return abi.encode(a, a); }\n',
     'bytes memory buf = S.h(a);\n'
     '        uint256 acc = 0;\n'
     '        for (uint256 i = 0; i < 2; ++i) {\n'
     '            acc += uint8(buf[33]);\n'
     '            buf = _shortBytes(bytes32(a));\n'
     '        }\n'
     '        root = acc + b;',
     '    function _shortBytes(bytes32 s) internal pure returns (bytes memory) {\n'
     '        bytes memory str = new bytes(32);\n'
     '        assembly ("memory-safe") {\n'
     '            mstore(str, 64)\n'
     '            mstore(add(str, 0x20), s)\n'
     '        }\n'
     '        return str;\n'
     '    }\n',
     'buf[33]',
     'byte index access on a ShortStrings assembly-allocated buffer is outside this slice'),
    ('short-string-byte-index-tuple',
     '    function h(uint256 a) external pure returns (uint256) { return a; }\n',
     '(bytes memory buf, uint256 tag) = _pair(_shortBytes(bytes32(a)));\n'
     '        root = uint8(buf[33]) + tag + S.h(b);',
     '    function _shortBytes(bytes32 s) internal pure returns (bytes memory) {\n'
     '        bytes memory str = new bytes(32);\n'
     '        assembly ("memory-safe") {\n'
     '            mstore(str, 64)\n'
     '            mstore(add(str, 0x20), s)\n'
     '        }\n'
     '        return str;\n'
     '    }\n'
     '    function _pair(bytes memory x) internal pure returns (bytes memory, uint256) {\n'
     '        return (x, 1);\n'
     '    }\n',
     'buf[33]',
     'byte index access on a ShortStrings assembly-allocated buffer is outside this slice'),
    ('short-string-byte-index-wrapped',
     '    function h(uint256 a) external pure returns (uint256) { return a; }\n',
     'root = uint8(bytes(_short(bytes32(a)))[33]) + S.h(b);',
     '    function _short(bytes32 s) internal pure returns (string memory) {\n'
     '        string memory str = new string(32);\n'
     '        assembly ("memory-safe") {\n'
     '            mstore(str, 64)\n'
     '            mstore(add(str, 0x20), s)\n'
     '        }\n'
     '        return str;\n'
     '    }\n',
     'bytes(_short(bytes32(a)))[33]',
     'byte index access on a ShortStrings assembly-allocated buffer is outside this slice'),
    ('function-typed-argument',
     '    function h(function (uint256) external returns (uint256) g) external pure returns (uint256) { return g.selector == bytes4(0) ? 1 : 0; }\n',
     'root = S.h(this.f2);', '    function f2(uint256 x) external returns (uint256) { return x; }\n',
     'function (uint256) external returns (uint256) g',
     'linked library call parameters must be value types or storage references'),
    ('msg-data',
     '    function h(uint256 a) external pure returns (uint256) { return msg.data.length + a; }\n',
     'root = S.h(a);', '', 'msg.data', 'msg.data and msg.sig in a linked library call'),
    ('paren-msg-sig',
     '    function h(uint256 a) external pure returns (uint256) { return uint32((msg).sig) + a; }\n',
     'root = S.h(a);', '', '(msg).sig', 'msg.data and msg.sig in a linked library call'),
    ('msg-sig-in-internal-helper',
     '    function g() internal pure returns (uint256) { return uint32(msg.sig); }\n'
     '    function h(uint256 a) external pure returns (uint256) { return g() + a; }\n',
     'root = S.h(a);', '', 'msg.sig', 'msg.data and msg.sig in a linked library call'),
    ('msg-data-in-modifier',
     '    modifier m() { require(msg.data.length > 4); _; }\n'
     '    function h(uint256 a) external pure m returns (uint256) { return a; }\n',
     'root = S.h(a);', '', 'msg.data', 'msg.data and msg.sig in a linked library call'),
    ('msg-sig-in-udvt-operator',
     '    function h(TaggedWord x, TaggedWord y) external pure returns (TaggedWord) { return x + y; }\n',
     'root = TaggedWord.unwrap(S.h(TaggedWord.wrap(a), TaggedWord.wrap(b)));', '',
     'msg.sig', 'msg.data and msg.sig in a linked library call'),
    ('gasleft',
     '    function h(uint256 a) external view returns (uint256) { return gasleft() + a; }\n',
     'root = S.h(a);', '', 'gasleft', 'gasleft() in a linked library call'),
    ('inline-assembly',
     '    function h(uint256 a) external pure returns (uint256 r) { assembly { r := add(a, 1) } }\n',
     'root = S.h(a);', '', 'assembly', 'inline assembly in a linked library call'),
]
# Frame cases the importer otherwise lowers, so the mutant must admit them. `gasleft` is also
# rejected elsewhere; the frame check rejects it first, as defense in depth.
FRAME_CASES = ('msg-data', 'paren-msg-sig', 'msg-sig-in-internal-helper',
               'msg-data-in-modifier', 'msg-sig-in-udvt-operator', 'inline-assembly')
# name -> (anchor, replacement, cases the mutant must admit)
MUTANTS = {
    'frame-check': (
        '  if let some (node, reason) := linkedLibraryFrameHazard? decl fn then\n',
        '  if let some (node, reason) := (none : Option (Json × String)) then\n',
        FRAME_CASES),
    'returndata-check': (
        '  unless env.rootLinkedLibraryCalls.isEmpty do\n    failAt j ("Yul returndatasize in a function',
        '  unless true do\n    failAt j ("Yul returndatasize in a function',
        ('returndatasize-after-call', 'bubbled-revert-after-call')),
    'alias-copy-in': (
        'private def copyLinkedBytesBuffer (srcPtr srcLen : Expr) (fromCalldata forReturn : Bool)\n'
        '    (siteNode : Json) (hint : String := "bytes_copy") : M EncodedBytes := do\n',
        'private def copyLinkedBytesBuffer (srcPtr srcLen : Expr) (fromCalldata forReturn : Bool)\n'
        '    (siteNode : Json) (hint : String := "bytes_copy") : M EncodedBytes := do\n'
        '  if !fromCalldata && !forReturn then\n'
        '    return { pre := #[], pointer := srcPtr, size := srcLen, ownedFresh := true }\n',
        ('bytes-copy-in-isolation',)),
    'drop-copy-out': (
        '  let alloc := AbiEncoding.reserve headerPtr finish totalBytes\n',
        '  if forReturn then\n'
        '    return { pre := #[], pointer := srcPtr, size := srcLen, ownedFresh := true }\n'
        '  let alloc := AbiEncoding.reserve headerPtr finish totalBytes\n',
        ('bytes-copy-out-disjoint',)),
}

GUARD_CASES = {
    'homonymous-file-udvt-clean': ([0x105, 10], 15),
    'bytes-copy-in-isolation': ([0x11, 0x22], 0x11aa77),
    'bytes-copy-out-disjoint': ([0x22, 0x99], 0x9922),
}


def run_case(output, name, library, body, members, token, diagnostic, cwd=None, with_guard=True):
    preamble = (UDVT_OPERATOR if 'TaggedWord' in library else
                SHADOW_UDVT_PREAMBLE if 'HomonymVal' in library else '')
    source = (PRAGMA + preamble + 'library S {\n' + STRUCT + library + '}\n' +
              CONTRACT.replace('{body}', body).replace('{members}', members))
    project = output / name
    project.mkdir()
    if 'HomonymVal' in library:
        for shadow in ('A_Shadow.sol', 'Z_Shadow.sol'):
            (project / shadow).write_text('pragma solidity 0.8.34;\ntype HomonymVal is uint256;\n')
    (project / 'Case.sol').write_text(source)
    extra = '' if name.startswith('flag-off') else ', linkedLibrariesMatchSource := true'
    guard = ''
    if with_guard and name in GUARD_CASES:
        call_args, expected_root = GUARD_CASES[name]
        args_lit = '[' + ', '.join(str(x) for x in call_args) + ']'
        guard = (
            'import Compiler.SolidityImport.Differential\n'
            '#guard match tested.model.functions.find? (·.name == "f") with\n'
            '  | none => false\n'
            '  | some fn =>\n'
            '    let r := Compiler.CompilationModel.Denote.denoteFunction\n'
            '      Compiler.CompilationModel.SolidityImport.Differential.oracle tested.model fn\n'
            f'      {{ sender := 1, functionSelector := 0, args := {args_lit} }} Verity.defaultState\n'
            f'    r.success && r.finalStorage 0 == {expected_root}\n')
    driver = project / 'Check.lean'
    driver.write_text('import Compiler.SolidityImport.Import\n'
        + ('import Compiler.SolidityImport.Differential\n' if guard else '') +
        'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
        f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
        f'  using {PROFILE.replace("{extra}", extra)}\n'
        '  contract C\n  function f(uint256, uint256)\n' +
        guard.replace('import Compiler.SolidityImport.Differential\n', ''))
    result = subprocess.run(['lake', 'env', 'lean', str(driver)], capture_output=True,
                            text=True, timeout=300, cwd=cwd)
    log = result.stdout + result.stderr
    (project / 'import.log').write_text(log)
    if token is None:
        return result.returncode == 0, log
    offset = source.index(token)
    line = source.count('\n', 0, offset) + 1
    column = offset - source.rfind('\n', 0, offset)
    location = f'Case.sol:{line}:{column}:'
    return result.returncode != 0 and diagnostic in log and location in log, log


def suite(output, cwd=None):
    output.mkdir(parents=True, exist_ok=False)
    results = []
    for name, library, body, members, token, diagnostic in CASES:
        ok, log = run_case(output, name, library, body, members, token, diagnostic, cwd)
        results.append({'case': name, 'ok': ok, 'diagnostic': diagnostic})
        write_json(output / 'results.json', results)
        if not ok:
            raise HarnessError(f'{name}: expected {diagnostic or "an import"}: {log[-3000:]}')
    write_json(output / 'complete.json', {'exit': 0, 'cases': len(CASES)})


def mutant(output, name):
    from .mutations import release, snapshot
    anchor, replacement, must_admit = MUTANTS[name]
    directory = output / 'snapshot'
    snapshot(directory)
    source = directory / 'Compiler/SolidityImport/Import.lean'
    original = source.read_text()
    if original.count(anchor) != 1:
        raise HarnessError('mutation anchor not unique')
    source.write_text(original.replace(anchor, replacement))
    command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=MUTANT_BUILD_TIMEOUT, log=output / 'build.log')
    admitted = []
    (output / 'admitted').mkdir()
    for case, library, body, members, _token, _diagnostic in CASES:
        if case in must_admit:
            ok, _ = run_case(output / 'admitted', case, library, body, members, None, None,
                             cwd=directory, with_guard=False)
            admitted.append({'case': case, 'admitted': ok})
    write_json(output / 'admitted.json', admitted)
    if len(admitted) != len(must_admit) or not all(row['admitted'] for row in admitted):
        raise HarnessError(f'{name} mutant did not admit every targeted case: {admitted}')
    env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))
    check = subprocess.run([sys.executable, '-m',
                            'solidity_differential.check_linked_library_call_rejections',
                            '--output', str(output / 'mutated')],
                           cwd=directory, env=env, capture_output=True, text=True, timeout=3600)
    (output / 'mutated.log').write_text(check.stdout + check.stderr)
    if check.returncode == 0:
        raise HarnessError(f'{name} mutant survived the rejection suite')
    release(directory)
    write_json(output / 'complete.json', {'exit': 0, 'mutant': name, 'detected': True})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutant', choices=tuple(MUTANTS))
    args = parser.parse_args()
    output = args.output.resolve()
    if args.mutant:
        output.mkdir(parents=True, exist_ok=False)
        mutant(output, args.mutant)
        print(f'linked library {args.mutant} mutant detected')
    else:
        suite(output)
        print(f'{len(CASES)} linked library call acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
