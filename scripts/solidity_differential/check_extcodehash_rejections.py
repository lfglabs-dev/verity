"""Located near-miss rejections and positive controls for `<address>.codehash` reads.

Each case is imported on its own. A positive control must elaborate and leave
an olean; a near miss must fail with the exact `Fixture.sol:line:column`
position of the named node, its construct and message, and leave no olean.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

MESSAGES = {
    'this-code-hash': 'code hash of the executing contract is unsupported',
    'error-argument': 'custom-error arguments currently require literals or scalar bindings',
    'self-alias': 'code hash of an account that may be the executing contract is unsupported',
    'self-alias-length': 'code length of an account that may be the executing contract is unsupported',
}

HASH_HELPER = ('    function hashOf(address target) internal view returns (bytes32) {\n'
               '        return target.codehash;\n    }\n')
PICK_HELPER = ('    function pick(address target, bool own) internal view returns (address) {\n'
               '        if (own) return address(this);\n        return target;\n    }\n')
OTHER_ROOT = ('    function other() external view returns (uint256) {\n'
              '        address self = address(this);\n        return uint256(uint160(self));\n    }\n')
# Extra contract members of a case, by case name.
MEMBERS = {'self-helper-code-hash': HASH_HELPER, 'helper-code-hash': HASH_HELPER,
           'self-helper-branch-code-hash': PICK_HELPER, 'second-root-name-reuse': OTHER_ROOT}
# Imported roots of a case, in import order (default: `checked(address)` only).
ROOTS = {'second-root-name-reuse': ['other()', 'checked(address)']}

# name, body, expected
# expected: None (positive control) or (marker, occurrence, construct, message key)
CASES = [
    ('compare-constant', 'if (account.codehash != BOUND) revert Unbound();\n        counter += 1;', None),
    ('require-equal', 'require(account.codehash == BOUND, Unbound());\n        counter += 1;', None),
    ('payable-account', 'last = payable(account).codehash;', None),
    ('bound-local', 'bytes32 found = account.codehash;\n        if (found == bytes32(0)) revert Unbound();\n'
     '        last = found;', None),
    ('this-code-hash', 'last = address(this).codehash;',
     ('address(this).codehash', 0, 'MemberAccess', 'this-code-hash')),
    ('this-code-hash-compare', 'if (address(this).codehash != BOUND) revert Unbound();',
     ('address(this).codehash', 0, 'MemberAccess', 'this-code-hash')),
    ('error-argument', 'if (account.codehash != BOUND) revert Found(account.codehash);',
     ('account.codehash)', 0, 'MemberAccess', 'error-argument')),
    # The lowered operand decides, not its syntax: aliases of address(this) reject.
    ('foreign-alias', 'address other = account;\n        last = other.codehash;', None),
    ('helper-code-hash', 'last = hashOf(account);', None),
    ('self-alias-code-hash', 'address self = address(this);\n        last = self.codehash;',
     ('self.codehash', 0, 'MemberAccess', 'self-alias')),
    ('self-reassigned-code-hash',
     'address target = account;\n        target = address(this);\n        last = target.codehash;',
     ('target.codehash', 0, 'MemberAccess', 'self-alias')),
    ('self-chained-code-hash',
     'address self = address(this);\n        address copy = self;\n        last = copy.codehash;',
     ('copy.codehash', 0, 'MemberAccess', 'self-alias')),
    ('self-helper-code-hash', 'last = hashOf(address(this));',
     ('target.codehash', 0, 'MemberAccess', 'self-alias')),
    ('self-alias-code-length', 'address self = address(this);\n        counter = self.code.length;',
     ('self.code', 0, 'MemberAccess', 'self-alias-length')),
    # address(this) reaching the operand through a branch or a tuple.
    ('self-conditional-code-hash',
     'last = (account == address(0) ? address(this) : account).codehash;',
     ('(account == address(0)', 0, 'MemberAccess', 'self-alias')),
    ('self-helper-branch-code-hash', 'last = pick(account, counter == 0).codehash;',
     ('pick(account', 0, 'MemberAccess', 'self-alias')),
    ('self-tuple-code-hash',
     '(address self, uint256 n) = (address(this), 1);\n        counter = n;\n        last = self.codehash;',
     ('self.codehash', 0, 'MemberAccess', 'self-alias')),
    # Assigned after the read in a loop body: the next iteration reads the contract itself.
    ('self-loop-carried-code-hash',
     'address target = account;\n        bytes32 found = bytes32(0);\n'
     '        for (uint256 i = 0; i < 2; i++) {\n            found = target.codehash;\n'
     '            target = address(this);\n        }\n        last = found;',
     ('target.codehash', 0, 'MemberAccess', 'self-alias')),
    # A self alias in one root does not reject a foreign alias of the same name in the next.
    ('second-root-name-reuse', 'address self = account;\n        last = self.codehash;', None),
]


def source(statements, members=''):
    return ('// SPDX-License-Identifier: MIT\npragma solidity 0.8.34;\n\n'
            'contract C {\n'
            '    bytes32 internal constant BOUND = bytes32(uint256(7));\n'
            '    error Unbound();\n    error Found(bytes32 found);\n'
            '    uint256 private counter;\n    bytes32 private last;\n'
            f'{members}'
            '    function checked(address account) external {\n'
            f'        {statements}\n    }}\n}}\n')


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
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='extcodehash-rejections-', dir=root / '.lake')))
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for name, statements, expected in CASES:
        if args.only and args.only != name:
            continue
        directory = output / name
        directory.mkdir()
        text = source(statements, MEMBERS.get(name, ''))
        roots = ''.join(f'  function {root}\n' for root in ROOTS.get(name, ['checked(address)']))
        (directory / 'Fixture.sol').write_text(text)
        driver = directory / 'Check.lean'
        driver.write_text(f'''import Compiler.SolidityImport.Import
solidity_import tested from "{directory}" entry "Fixture.sol"
  using {{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }}
  contract C
{roots}''')
        artifact = directory / 'Check.olean'
        result = subprocess.run(['lake', 'env', 'lean', str(driver), '-o', str(artifact)],
                                cwd=root, text=True, capture_output=True, timeout=300)
        log = result.stdout + result.stderr
        (directory / 'check.log').write_text(log)
        if expected is None:
            if result.returncode or not artifact.exists():
                raise SystemExit(f'{name}: positive control failed\n{log}')
            diagnostic = None
        else:
            marker, occurrence, construct, key = expected
            line, column = location(text, marker, occurrence)
            diagnostic = (f'Fixture.sol:{line}:{column}: {construct}: '
                          f'[solidity-import:unsupported] {MESSAGES[key]}')
            if result.returncode == 0 or artifact.exists() or diagnostic not in log:
                raise SystemExit(f'{name}: expected exact located rejection {diagnostic!r}\n{log}')
        results.append({'case': name, 'diagnostic': diagnostic,
                        'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        (output / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        print(f'pass extcodehash-{name}', flush=True)
    print(f'code-hash rejections passed: {output}')


if __name__ == '__main__':
    main()
