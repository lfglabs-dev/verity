"""Located rejections and acceptances for linked library calls under
`linkedLibrariesMatchSource := true` (#2728).

With the trust assumption on, a direct `L.f(...)` DELEGATECALL inlines `f`'s body only when
the arguments are value types or storage references, the results are value types and nothing
the body reaches (internal helpers and modifiers, transitively) depends on the DELEGATECALL
frame. Each case below must reject at the stated token with the stated diagnostic, or import.
Without the flag the same calls keep the `check_library_call_rejections` diagnostic.

`--mutant frame-check` (or `returndata-check`) builds a snapshot with that guard disabled,
requires the cases it guards to import there, then this suite to fail on that snapshot.
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
     'root = S.h(abi.encode(a, b));', '', 'bytes memory data',
     'linked library call parameters must be value types or storage references'),
    ('memory-result',
     '    function h(uint256 a) external pure returns (bytes memory) { return abi.encode(a); }\n',
     'root = S.h(a).length;', '', 'bytes memory)',
     'linked library call results must be value types'),
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
}


def run_case(output, name, library, body, members, token, diagnostic, cwd=None):
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
    if name == 'homonymous-file-udvt-clean':
        guard = (
            'import Compiler.SolidityImport.Differential\n'
            '#guard match tested.model.functions.find? (·.name == "f") with\n'
            '  | none => false\n'
            '  | some fn =>\n'
            '    let r := Compiler.CompilationModel.Denote.denoteFunction\n'
            '      Compiler.CompilationModel.SolidityImport.Differential.oracle tested.model fn\n'
            '      { sender := 1, functionSelector := 0, args := [0x105, 10] } Verity.defaultState\n'
            '    r.success && r.finalStorage 0 == 15\n')
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
    from .mutations import snapshot
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
                             cwd=directory)
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
