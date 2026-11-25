"""Located rejections and acceptances for linked library calls under
`linkedLibrariesMatchSource := true` (#2728).

With the trust assumption on, a direct `L.f(...)` DELEGATECALL inlines `f`'s body only when
the arguments are value types or storage references, the results are value types and nothing
the body reaches (internal helpers and modifiers, transitively) depends on the DELEGATECALL
frame. Each case below must reject at the stated token with the stated diagnostic, or import.
Without the flag the same calls keep the `check_library_call_rejections` diagnostic.

`--mutant` builds a snapshot whose frame check is disabled and requires the frame cases to
import there, then this suite to fail on that snapshot (mutation detection).
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
    ('msg-sig-in-internal-helper',
     '    function g() internal pure returns (uint256) { return uint32(msg.sig); }\n'
     '    function h(uint256 a) external pure returns (uint256) { return g() + a; }\n',
     'root = S.h(a);', '', 'msg.sig', 'msg.data and msg.sig in a linked library call'),
    ('msg-data-in-modifier',
     '    modifier m() { require(msg.data.length > 4); _; }\n'
     '    function h(uint256 a) external pure m returns (uint256) { return a; }\n',
     'root = S.h(a);', '', 'msg.data', 'msg.data and msg.sig in a linked library call'),
    ('gasleft',
     '    function h(uint256 a) external view returns (uint256) { return gasleft() + a; }\n',
     'root = S.h(a);', '', 'gasleft', 'gasleft() in a linked library call'),
    ('inline-assembly',
     '    function h(uint256 a) external pure returns (uint256 r) { assembly { r := add(a, 1) } }\n',
     'root = S.h(a);', '', 'assembly', 'inline assembly in a linked library call'),
]
# Frame cases the importer otherwise lowers, so the mutant must admit them. `gasleft` is also
# rejected elsewhere; the frame check rejects it first, as defense in depth.
FRAME_CASES = ('msg-data', 'msg-sig-in-internal-helper', 'msg-data-in-modifier',
               'inline-assembly')
MUTANT_ANCHOR = '  if let some (node, reason) := linkedLibraryFrameHazard? decl fn then\n'
MUTANT_REPLACEMENT = '  if let some (node, reason) := (none : Option (Json × String)) then\n'


def run_case(output, name, library, body, members, token, diagnostic, cwd=None):
    source = (PRAGMA + 'library S {\n' + STRUCT + library + '}\n' +
              CONTRACT.replace('{body}', body).replace('{members}', members))
    project = output / name
    project.mkdir()
    (project / 'Case.sol').write_text(source)
    extra = '' if name.startswith('flag-off') else ', linkedLibrariesMatchSource := true'
    driver = project / 'Check.lean'
    driver.write_text('import Compiler.SolidityImport.Import\n'
        'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
        f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
        f'  using {PROFILE.replace("{extra}", extra)}\n'
        '  contract C\n  function f(uint256, uint256)\n')
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


def mutant(output):
    from .mutations import snapshot
    directory = output / 'snapshot'
    snapshot(directory)
    source = directory / 'Compiler/SolidityImport/Import.lean'
    original = source.read_text()
    if original.count(MUTANT_ANCHOR) != 1:
        raise HarnessError('mutation anchor not unique')
    source.write_text(original.replace(MUTANT_ANCHOR, MUTANT_REPLACEMENT))
    command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=MUTANT_BUILD_TIMEOUT, log=output / 'build.log')
    admitted = []
    (output / 'admitted').mkdir()
    for name, library, body, members, _token, _diagnostic in CASES:
        if name in FRAME_CASES:
            ok, _ = run_case(output / 'admitted', name, library, body, members, None, None,
                             cwd=directory)
            admitted.append({'case': name, 'admitted': ok})
    write_json(output / 'admitted.json', admitted)
    if not all(row['admitted'] for row in admitted):
        raise HarnessError(f'mutant did not admit every frame case: {admitted}')
    env = dict(os.environ, PYTHONPATH=str(directory / 'scripts'))
    check = subprocess.run([sys.executable, '-m',
                            'solidity_differential.check_linked_library_call_rejections',
                            '--output', str(output / 'mutated')],
                           cwd=directory, env=env, capture_output=True, text=True, timeout=3600)
    (output / 'mutated.log').write_text(check.stdout + check.stderr)
    if check.returncode == 0:
        raise HarnessError('frame-check mutant survived the rejection suite')
    write_json(output / 'complete.json', {'exit': 0, 'mutant': 'frame-check', 'detected': True})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutant', action='store_true')
    args = parser.parse_args()
    output = args.output.resolve()
    if args.mutant:
        output.mkdir(parents=True, exist_ok=False)
        mutant(output)
        print('linked library frame-check mutant detected')
    else:
        suite(output)
        print(f'{len(CASES)} linked library call acceptance/rejection controls pass')


if __name__ == '__main__':
    main()
