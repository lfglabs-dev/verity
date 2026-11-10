"""Lowering checks for address immutables without an inline initializer.

Each case is imported on its own and the model is printed. An immutable that the chain's
constructors assign exactly once, at the top level of a constructor body, to `address(this)`
must read as `Expr.contractAddress`. Every other one must read as `Expr.immutable NAME`, be
declared in `model.immutables`, and be installed by the synthesized constructor from its
argument, in declaration order. A case passes only if the printed model matches exactly
these expectations; immutables with an inline initializer keep their located rejection.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HEADER = '// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'

# name, source, roots, expected
# expected: ('model', unknown immutables in declaration order, immutables read as address(this))
#        or ('reject', marker, construct, message)
CASES = [
    ('constructor-argument',
     'contract C {\n    address private immutable GUARD;\n'
     '    constructor(address guard_) { GUARD = guard_; }\n'
     '    function f() external view returns (bool) { return msg.sender == GUARD; }\n}\n',
     ['f()'], ('model', ['GUARD'], [])),
    ('self-top-level',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor(uint256 x) { require(x != 0, "zero"); SELF = address(this); }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', [], ['SELF'])),
    ('self-conditional',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor(bool flag_, address other_) {\n'
     '        if (flag_) { SELF = address(this); } else { SELF = other_; }\n    }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    ('self-assigned-twice',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor(address other_) { SELF = other_; SELF = address(this); }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    ('self-through-local',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor() { address me = address(this); SELF = me; }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    ('inherited-and-ordered',
     'abstract contract Base {\n    address internal immutable FIRST;\n'
     '    constructor(address first_) { FIRST = first_; }\n}\n'
     'contract C is Base {\n    address private immutable SECOND;\n    address private immutable SELF;\n'
     '    constructor(address first_, address second_) Base(first_) {\n'
     '        SECOND = second_;\n        SELF = address(this);\n    }\n'
     '    function f() external view returns (bool) {\n'
     '        return msg.sender == FIRST || msg.sender == SECOND || address(this) == SELF;\n    }\n}\n',
     ['f()'], ('model', ['FIRST', 'SECOND'], ['SELF'])),
    ('custom-error-guard',
     'contract C {\n    address private immutable GUARD;\n    uint256 private value;\n'
     '    error NotGuard(address caller);\n'
     '    constructor(address guard_) { GUARD = guard_; }\n'
     '    function set(uint256 x) external { require(msg.sender == GUARD, NotGuard(msg.sender)); value = x; }\n}\n',
     ['set(uint256)'], ('model', ['GUARD'], [])),
    ('inline-initializer',
     'contract C {\n    address private immutable SELF = address(this);\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('reject', 'SELF;', 'Identifier', 'immutable state variable SELF is outside this slice')),
]


def location(text, marker):
    start = text.index(marker)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def expected_lines(unknown, selves):
    lines = [f'immutable {name} {i}' for i, name in enumerate(unknown)]
    lines.append(f'constructor {"some" if unknown else "none"}')
    lines += [f'reads-immutable {name}' for name in unknown]
    lines += [f'not-read-as-immutable {name}' for name in selves]
    lines.append(f'reads-contract-address {"true" if selves else "any"}')
    return lines


def driver(directory, roots, unknown, selves):
    names = json.dumps(unknown + selves)
    functions = '\n'.join(f'  function {root}' for root in roots)
    return f'''import Compiler.SolidityImport.Import
open Compiler.CompilationModel
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
{functions}
#eval show IO Unit from do
  let m := tested.model
  for (imm, i) in m.immutables.zipIdx do
    unless (repr imm.init).pretty == (repr (Expr.constructorArg i)).pretty do
      throw (IO.userError s!"immutable {{imm.name}} is not installed from argument {{i}}")
    IO.println s!"immutable {{imm.name}} {{i}}"
  IO.println s!"constructor {{if m.constructor.isSome then "some" else "none"}}"
  let body := toString (repr (m.functions.map (·.body)))
  for name in ({names} : List String) do
    if (body.splitOn s!"Expr.immutable \\"{{name}}\\"").length > 1 then
      IO.println s!"reads-immutable {{name}}"
    else
      IO.println s!"not-read-as-immutable {{name}}"
  IO.println s!"reads-contract-address {{if (body.splitOn "Expr.contractAddress").length > 1 then "true" else "false"}}"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    root = Path.cwd()
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='immutable-lowering-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, body, roots, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = HEADER + body
        (directory / 'Fixture.sol').write_text(text)
        unknown, selves = (expected[1], expected[2]) if expected[0] == 'model' else ([], [])
        (directory / 'Check.lean').write_text(driver(directory, roots, unknown, selves))
        result = subprocess.run(['lake', 'env', 'lean', str(directory / 'Check.lean')],
                                cwd=root, text=True, capture_output=True, timeout=600)
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if expected[0] == 'model':
            if result.returncode:
                raise SystemExit(f'{name}: import failed\n{log}')
            seen = [line for line in log.splitlines() if line.split(' ')[0] in (
                'immutable', 'constructor', 'reads-immutable', 'not-read-as-immutable',
                'reads-contract-address')]
            want = expected_lines(unknown, selves)
            got = [line for line in seen if not (line.startswith('reads-contract-address') and
                                                 want[-1].endswith('any'))]
            want = [line for line in want if not line.endswith(' any')]
            if got != want:
                raise SystemExit(f'{name}: lowering differs\n  want {want}\n  got  {got}\n{log}')
            diagnostic = None
        else:
            _, marker, construct, message = expected
            line, column = location(text, marker)
            diagnostic = f'Fixture.sol:{line}:{column}: {construct}: [solidity-import:unsupported] {message}'
            if result.returncode == 0 or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass immutable-lowering-{name}', flush=True)
    print(f'immutable lowering checks passed: {output}')


if __name__ == '__main__':
    main()
