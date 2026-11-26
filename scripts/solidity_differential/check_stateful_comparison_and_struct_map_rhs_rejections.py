"""Located near-miss rejections and positive controls for stateful comparisons and
storage-struct mapping RHS assignments (#2976).

Each case is imported on its own inside `.lake/` (never `/tmp`, one case per file).
A positive control must elaborate and leave an `.olean`; a near miss must fail with
the exact `Fixture.sol:line:column` position, AST construct and diagnostic message,
and leave no `.olean`.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

FIXTURE = Path('Contracts/SolidityImportSmoke/StatefulComparisonStructMapRhsRejections.sol')
POSITIVE_FIXTURE = Path('Contracts/SolidityImportSmoke/StatefulComparisonStructMapRhs.sol')

PROFILE = ('{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, '
           'bytecodeHash := "none", linkedLibrariesMatchSource := true }')
PAYABLE_PROFILE = ('{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, '
                   'bytecodeHash := "none" }')

# (name, source_path, contract, function_sig, profile, expected)
# expected is None for positive controls, or (marker, construct, diagnostic_substring).
CASES = [
    ('positive-comparison-via-ir', POSITIVE_FIXTURE, 'StatefulComparisonStructMapRhs',
     'assertDeployMatch(address,bytes,address)', PROFILE, None),
    ('positive-comparison-legacy', POSITIVE_FIXTURE, 'StatefulComparisonStructMapRhs',
     'compareCallAndState(address,uint256,uint256,address)',
     PROFILE.replace('viaIR := true', 'viaIR := false'), None),
    ('positive-struct-map-direct-key', POSITIVE_FIXTURE, 'StatefulComparisonStructMapRhs',
     'setDirectKeyInternal(address,bytes32,bytes32,bytes)', PROFILE, None),
    ('positive-struct-map-computed-key-linked', POSITIVE_FIXTURE, 'StatefulComparisonStructMapRhs',
     'setComputedKeyLinked(address,bytes32,address,bytes4,uint256)', PROFILE, None),
    ('positive-struct-map-side-effect-keys', POSITIVE_FIXTURE, 'StatefulComparisonStructMapRhs',
     'setSideEffectKeysOrder(address,uint256,bytes32,address,bytes4,uint256)', PROFILE, None),
    ('arithmetic-stateful-operand', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'arithmeticWithStatefulOperand(uint256)', PROFILE,
     ('_bump() + x', 'BinaryOperation',
      'stateful helper operands require explicit evaluation-order support')),
    ('bitwise-stateful-operand', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'bitwiseWithStatefulOperand(uint256)', PROFILE,
     ('x | _bump()', 'BinaryOperation',
      'stateful helper operands require explicit evaluation-order support')),
    ('user-defined-eq-stateful-operand', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'userDefinedEqWithStatefulOperand(uint256)', PROFILE,
     ('WrappedUint.wrap(x) == _bumpWrapped()', 'BinaryOperation',
      'stateful helper operands require explicit evaluation-order support')),
    ('comparison-assignment-operand', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'comparisonWithAssignmentOperand(uint256)', PROFILE,
     ('(y = x + 1) == _bump()', 'BinaryOperation',
      'stateful helper operands require explicit evaluation-order support')),
    ('comparison-memory-write-hazard', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'comparisonWithMemoryWriteHazard(uint256)', PROFILE,
     ('arr[0] == _writeMem(arr)', 'BinaryOperation',
      'stateful helper operands require explicit evaluation-order support')),
    ('comparison-pure-memory-write-hazard', FIXTURE, 'StatefulComparisonStructMapRhsRejections',
     'comparisonWithPureMemoryWriteHazard(uint256)', PROFILE,
     ('arr[0] == _writeMemPure(arr)', 'BinaryOperation',
      'memory-writing helper operands require explicit evaluation-order support')),
    ('flat-mapping-computed-key-interface-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'flatMappingComputedKeyInterfaceRhs(address,address,bytes4)', PROFILE,
     ('INearMissOracle(oracle).peekUint()', 'FunctionCall',
      'typed interface staticcall in an assignment to an array element or computed key is unsupported: '
      'solc evaluates the right-hand side first')),
    ('struct-mapping-compound-interface-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structMappingCompoundInterfaceRhs(address,bytes32,address,bytes4)', PROFILE,
     ('INearMissOracle(oracle).peekUint()', 'FunctionCall',
      'typed interface staticcall in an assignment to an array element or computed key is unsupported: '
      'solc evaluates the right-hand side first')),
    ('struct-mapping-compound-stateful-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structMappingCompoundStatefulRhs(bytes32,address,bytes4)', PROFILE,
     ('buckets[bucketKey].entries[_packKey(targetAddr, sel)]', 'IndexAccess',
      'compound mapping write key prelude with stateful RHS is unsupported')),
    ('struct-mapping-interface-call-in-key', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structMappingInterfaceCallInKey(address,bytes32)', PROFILE,
     ('INearMissOracle(oracle).peekBytes32()', 'FunctionCall',
      'typed interface staticcall in an assignment to an array element or computed key is unsupported: '
      'solc evaluates the right-hand side first')),
    ('struct-mapping-assignment-in-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structMappingAssignmentInRhs(bytes32,address,bytes4)', PROFILE,
     ('buckets[bucketKey].entries[_packKey(targetAddr, sel)]', 'IndexAccess',
      'struct mapping write key prelude with stateful RHS is unsupported')),
    ('struct-dynamic-array-stateful-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structDynamicArrayStatefulRhs(bytes32)', PROFILE,
     ('buckets[bucketKey].dynValues[0]', 'IndexAccess',
      'struct dynamic array write index prelude with stateful RHS is unsupported')),
    ('struct-fixed-array-interface-rhs', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'structFixedArrayInterfaceRhs(address,bytes32)', PROFILE,
     ('INearMissOracle(oracle).peekUint()', 'FunctionCall',
      'typed interface staticcall in an assignment to an array element or computed key is unsupported: '
      'solc evaluates the right-hand side first')),
    ('value-call-before-struct-mapping-write', FIXTURE,
     'StatefulComparisonStructMapRhsRejections',
     'valueCallBeforeStructMappingWrite(address,bytes32,bytes32)', PAYABLE_PROFILE,
     ('function valueCallBeforeStructMappingWrite', 'FunctionDefinition',
      'storage reads, storage writes and logs after an external CALL are supported only when '
      'every external interaction of the function is a closed transport')),
]


def marker_site(text: str, function_sig: str, marker: str) -> tuple[int, int]:
    fn_name = function_sig.split('(', 1)[0]
    fn_idx = text.find(f'function {fn_name}')
    if fn_idx < 0:
        raise RuntimeError(f'missing function {fn_name!r}')
    idx = text.find(marker, fn_idx)
    if idx < 0:
        raise RuntimeError(f'missing marker {marker!r} in {fn_name!r}')
    line = text.count('\n', 0, idx) + 1
    col = idx - text.rfind('\n', 0, idx)
    return line, col


def run_case(base_dir: Path, name: str, source_path: Path, contract: str, function_sig: str,
             profile: str, expected) -> dict:
    case_dir = base_dir / name
    case_dir.mkdir(parents=True, exist_ok=True)
    source_text = source_path.read_text(encoding='utf-8')
    (case_dir / 'Fixture.sol').write_text(source_text, encoding='utf-8')
    driver = case_dir / 'Case.lean'
    olean = case_dir / 'Case.olean'
    if olean.exists():
        olean.unlink()
    driver.write_text(
        f'import Compiler.SolidityImport.Import\n'
        f'solidity_import checked from "{case_dir}" entry "Fixture.sol"\n'
        f'  using {profile}\n'
        f'  contract {contract}\n'
        f'  function {function_sig}\n',
        encoding='utf-8',
    )
    res = subprocess.run(
        ['lake', 'env', 'lean', str(driver), '-o', str(olean)],
        text=True, capture_output=True, timeout=900,
    )
    log = res.stdout + res.stderr
    (case_dir / 'Case.log').write_text(log, encoding='utf-8')
    if expected is None:
        if res.returncode != 0 or not olean.exists():
            raise SystemExit(f'{name}: positive control failed:\n{log}')
        return {'name': name, 'kind': 'positive', 'passed': True}
    marker, construct, diagnostic = expected
    line, col = marker_site(source_text, function_sig, marker)
    needle = f'Fixture.sol:{line}:{col}: {construct}: [solidity-import:unsupported] {diagnostic}'
    if res.returncode == 0 or olean.exists() or needle not in log:
        raise SystemExit(f'{name}: expected located rejection:\n  {needle}\ngot:\n{log}')
    return {'name': name, 'kind': 'rejection', 'site': f'{line}:{col}', 'passed': True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', help='run a single named case')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    Path('.lake').mkdir(exist_ok=True)
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='stateful-cmp-rhs-rejections-', dir='.lake')).resolve())
    output.mkdir(parents=True, exist_ok=True)
    selected = [c for c in CASES if args.only is None or c[0] == args.only]
    if not selected:
        parser.error(f'unknown case {args.only!r}')
    rows = [run_case(output, *case) for case in selected]
    print(f'stateful comparison & struct-mapping RHS rejections passed ({len(rows)} cases): {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
