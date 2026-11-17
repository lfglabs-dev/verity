"""Lowering checks for immutables.

Each case is imported on its own and the model is printed. An address immutable that the
chain's constructors assign exactly once, at the top level of a constructor body, to
`address(this)` must read as `Expr.contractAddress`. An immutable any constructor writes must
read as `Expr.immutable NAME`, be declared in `model.immutables`, and be installed by the
synthesized constructor from an argument of its type, in declaration order. One never written
whose inline initializer reads the deployment environment must be installed from that
initializer; one never written whose value the source fixes (no initializer, or a literal
one) must read as that value. A case passes only if the printed model matches exactly these
expectations; other inline initializers and enum-typed immutables keep a located rejection.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HEADER = '// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'

# name, source, roots, expected
# expected: ('model', argument immutables in declaration order, immutables not read as
#            `Expr.contractAddress`[, installed (name, initializer) pairs[, argument types
#            [, immutables read as the value the source fixes]]]])
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
    # Writes other than a plain assignment count too: solc >= 0.8.21 accepts each of these.
    ('self-tuple-rewrite',
     'contract C {\n    address private immutable SELF;\n    uint256 private y;\n'
     '    constructor(address other_) { SELF = address(this); (SELF, y) = (other_, 1); }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    ('self-delete',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor() { SELF = address(this); delete SELF; }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    # The assignment must run on every deployment: an early return or a modifier that skips
    # the body leaves the immutable zero.
    ('self-after-early-return',
     'contract C {\n    address private immutable SELF;\n'
     '    constructor(bool skip_) { if (skip_) return; SELF = address(this); }\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', ['SELF'], [])),
    ('self-under-skipping-modifier',
     'contract C {\n    address private immutable SELF;\n'
     '    modifier unless(bool skip_) { if (!skip_) { _; } }\n'
     '    constructor(bool skip_) unless(skip_) { SELF = address(this); }\n'
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
    # An inline `address(this)` initializer is evaluated by the synthesized constructor; the
    # read stays `Expr.immutable`, so no self-address assumption is made for it.
    ('inline-initializer',
     'contract C {\n    address private immutable SELF = address(this);\n'
     '    function f() external view returns (bool) { return address(this) == SELF; }\n}\n',
     ['f()'], ('model', [], [], [('SELF', 'Expr.contractAddress')])),
    # Scalar and contract-typed immutables written by a constructor are arguments of their type.
    ('scalar-arguments',
     'interface IT { function totalSupply() external view returns (uint256); }\n'
     'contract C {\n    uint256 private immutable A;\n    uint64 private immutable B;\n'
     '    uint8 private immutable D;\n    bool private immutable E;\n    bytes32 private immutable F;\n'
     '    int16 private immutable G;\n    IT private immutable H;\n    address payable private immutable P;\n'
     '    bytes4 private immutable Q;\n'
     '    constructor(uint256 a, uint64 b, uint8 d, bool e, bytes32 f, int16 g, IT h, address payable p,\n'
     '        bytes4 q) {\n'
     '        A = a; B = b; D = d; E = e; F = f; G = g; H = h; P = p; Q = q;\n    }\n'
     '    function f() external view returns (uint256, uint64, uint8, bool, bytes32, int16, address,\n'
     '        address, bytes4) {\n'
     '        return (A, B, D, E, F, G, address(H), P, Q);\n    }\n}\n',
     ['f()'], ('model', ['A', 'B', 'D', 'E', 'F', 'G', 'H', 'P', 'Q'], [], [],
               ['uint256', 'uintN 64', 'uintN 8', 'bool', 'bytes32', 'intN 16', 'address', 'address',
                'bytesN 4'])),
    # Any constructor write makes an argument: conditional, repeated, over an inline initializer.
    ('scalar-conditional-write',
     'contract C {\n    uint8 private immutable D;\n'
     '    constructor(uint8 d) { if (d > 18) { D = 18; } else { D = d; } }\n'
     '    function f() external view returns (uint8) { return D; }\n}\n',
     ['f()'], ('model', ['D'], [])),
    ('initializer-then-written',
     'contract C {\n    uint256 private immutable X = 1;\n'
     '    constructor(uint256 a) { X = a; X = X + 1; }\n'
     '    function f() external view returns (uint256) { return X; }\n}\n',
     ['f()'], ('model', ['X'], [])),
    ('initializer-environment',
     'contract C {\n    address private immutable OWNER = msg.sender;\n'
     '    uint256 private immutable CHAIN = block.chainid;\n'
     '    function f() external view returns (bool) { return msg.sender == OWNER && block.chainid == CHAIN; }\n}\n',
     ['f()'], ('model', [], [], [('OWNER', 'Expr.caller'), ('CHAIN', 'Expr.chainid')])),
    ('initializer-literal',
     'contract C {\n    uint256 private immutable SCALE = 1e6;\n'
     '    function f(uint256 x) external view returns (uint256) { return x / SCALE; }\n}\n',
     ['f(uint256)'], ('model', [], [], [], None, ['SCALE'])),
    ('never-written',
     'contract C {\n    uint256 private immutable UNSET;\n'
     '    function f() external view returns (uint256) { return UNSET; }\n}\n',
     ['f()'], ('model', [], [], [], None, ['UNSET'])),
    ('public-getter',
     'contract C {\n    uint64 public immutable START;\n'
     '    constructor(uint64 s) { START = s; }\n}\n',
     ['START()'], ('model', ['START'], [], [], ['uintN 64'])),
    # Initializers that read storage or need statements are not modeled: the read rejects.
    ('initializer-storage-rejected',
     'contract C {\n    uint256 private y = 5;\n    uint256 private immutable X = y;\n'
     '    function f() external view returns (uint256) { return X; }\n}\n',
     ['f()'], ('reject', 'X; }', 'Identifier', 'immutable state variable X is outside this slice')),
    ('initializer-hash-rejected',
     'contract C {\n    bytes32 private immutable H = keccak256(abi.encode(msg.sender));\n'
     '    function f() external view returns (bytes32) { return H; }\n}\n',
     ['f()'], ('reject', 'H; }', 'Identifier', 'immutable state variable H is outside this slice')),
    ('enum-rejected',
     'contract C {\n    enum K { A, B }\n    K private immutable KIND;\n'
     '    constructor(K k) { KIND = k; }\n'
     '    function f() external view returns (uint256) { return uint256(KIND); }\n}\n',
     ['f()'], ('reject', 'KIND); }', 'Identifier', 'immutable state variable KIND is outside this slice')),
]


def location(text, marker):
    start = text.index(marker)
    before = text.encode()[:len(text[:start].encode())]
    line = before.count(b'\n') + 1
    column = len(before) - (before.rfind(b'\n') + 1) + 1
    return line, column


def expected_lines(unknown, selves, installed=(), types=None, fixed=()):
    lines = [f'immutable {name} {i}' for i, name in enumerate(unknown)]
    lines += [f'installed {name} {init}' for name, init in installed]
    lines += [f'argument-type {name} {ty}' for name, ty in zip(unknown, types or [])]
    lines.append(f'constructor {"some" if unknown or installed else "none"}')
    lines += [f'reads-immutable {name}' for name in unknown]
    lines += [f'reads-immutable {name}' for name, _ in installed]
    lines += [f'not-read-as-immutable {name}' for name in list(selves) + list(fixed)]
    lines.append(f'reads-contract-address {"true" if selves else "any"}')
    return lines


def driver(directory, roots, unknown, selves, installed=(), types=None, fixed=()):
    names = json.dumps(unknown + [name for name, _ in installed] + selves + list(fixed))
    installed_names = json.dumps([name for name, _ in installed])
    typed = 'true' if types else 'false'
    functions = '\n'.join(f'  function {root}' for root in roots)
    return f'''import Compiler.SolidityImport.Import
open Compiler.CompilationModel
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
{functions}
#eval show IO Unit from do
  let m := tested.model
  let params := (m.constructor.map (·.params)).getD []
  let mut i := 0
  for imm in m.immutables do
    if ({installed_names} : List String).contains imm.name then
      IO.println s!"installed {{imm.name}} {{(repr imm.init).pretty}}"
      continue
    unless (repr imm.init).pretty == (repr (Expr.constructorArg i)).pretty do
      throw (IO.userError s!"immutable {{imm.name}} is not installed from argument {{i}}")
    let some p := params[i]? | throw (IO.userError s!"no constructor parameter {{i}}")
    unless p.name == imm.name && (repr p.ty).pretty == (repr imm.ty).pretty do
      throw (IO.userError s!"constructor parameter {{i}} is not immutable {{imm.name}}")
    IO.println s!"immutable {{imm.name}} {{i}}"
    i := i + 1
  for imm in m.immutables do
    unless ({installed_names} : List String).contains imm.name do
      if {typed} then
        IO.println s!"argument-type {{imm.name}} {{(repr imm.ty).pretty}}"
  unless params.length == i do throw (IO.userError "constructor takes extra arguments")
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
        installed = expected[3] if expected[0] == 'model' and len(expected) > 3 else []
        types = expected[4] if expected[0] == 'model' and len(expected) > 4 else None
        fixed = expected[5] if expected[0] == 'model' and len(expected) > 5 else []
        (directory / 'Check.lean').write_text(
            driver(directory, roots, unknown, selves, installed, types, fixed))
        result = subprocess.run(['lake', 'env', 'lean', str(directory / 'Check.lean')],
                                cwd=root, text=True, capture_output=True, timeout=600)
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if expected[0] == 'model':
            if result.returncode:
                raise SystemExit(f'{name}: import failed\n{log}')
            seen = [line for line in log.splitlines() if line.split(' ')[0] in (
                'immutable', 'installed', 'argument-type', 'constructor', 'reads-immutable',
                'not-read-as-immutable', 'reads-contract-address')]
            want = expected_lines(unknown, selves, installed, types, fixed)
            got = [line.replace('Compiler.CompilationModel.', '').replace('ParamType.', '')
                   for line in seen if not (line.startswith('reads-contract-address') and
                                            want[-1].endswith('any'))]
            want = [line for line in want if not line.endswith(' any')]
            # Argument indices fix the order; the model lists every immutable in one order.
            if sorted(got) != sorted(want):
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
