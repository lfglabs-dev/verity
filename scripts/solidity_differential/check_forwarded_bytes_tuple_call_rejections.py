"""Located near-miss rejections and positive controls for typed external
`(Scalar, bytes memory)` interface calls in forwarded tuple call trees
(Refs #2803, Refs #2842).

Each case is imported on its own in `.lake/`. Positive controls must elaborate;
near misses must fail with the exact construct and diagnostic message.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import tempfile


CASES = [
    # Positive control: nonpayable (bool, bytes memory) with post-call write
    (
        'positive-bool-bytes',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(address to, uint256 v, bytes memory d) external returns (bool, bytes memory);
}
contract C {
    address public target;
    uint256 public count;
    function _run(address to, uint256 v, bytes calldata d) private returns (bool ok, bytes memory out) {
        (ok, out) = ITarget(target).run(to, v, d);
        if (ok) count += 1;
    }
    function run(address to, uint256 v, bytes calldata d) external returns (bool ok, bytes memory out) {
        return _run(to, v, d);
    }
}
""",
        'run(address,uint256,bytes)',
        None,
    ),
    # Positive control: view (uint16, bytes memory)
    (
        'positive-view-uint16-bytes',
        """pragma solidity 0.8.34;
interface ITarget {
    function peek(uint256 x) external view returns (uint16, bytes memory);
}
contract C {
    address public target;
    function _peek(uint256 x) private view returns (uint16 tag, bytes memory out) {
        (tag, out) = ITarget(target).peek(x);
    }
    function peek(uint256 x) external view returns (uint16 tag, bytes memory out) {
        return _peek(x);
    }
}
""",
        'peek(uint256)',
        None,
    ),
    # Rejection: payable interface function
    (
        'reject-payable-interface',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external payable returns (bool, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (ok, out) = ITarget(target).run(x);
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] typed external (scalar, bytes memory) call must be nonpayable, view or pure',
    ),
    # Rejection: unsupported narrow signed scalar return (int8)
    (
        'reject-int8-scalar-return',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external returns (int8, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (int8 v, bytes memory out) {
        (v, out) = ITarget(target).run(x);
    }
    function run(uint256 x) external returns (int8 v, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] typed external (scalar, bytes memory) call scalar return must be uint256, uint8..uint248, int256, bytes32, bytes4, bytes1, bool, address or enum',
    ),
    # Rejection: 3-tuple return arity
    (
        'reject-arity-3-tuple',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external returns (bool, uint256, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        uint256 extra;
        (ok, extra, out) = ITarget(target).run(x);
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'Assignment: [solidity-import:unsupported] forwarded bytes result requires assignment from abi.encode or abi.encodePacked',
    ),
    # Rejection: (bool, string memory) instead of (bool, bytes memory)
    (
        'reject-string-second-component',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external returns (bool, string memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (bool ok2, string memory s) = ITarget(target).run(x);
        ok = ok2;
        out = abi.encodePacked(s);
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'FunctionCall: [solidity-import:unsupported] typed external call results are unsupported in a forwarded tuple call tree',
    ),
    # Rejection: effectful argument in external tuple call
    (
        'reject-effectful-arg',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external returns (bool, bytes memory);
}
contract C {
    address public target;
    uint256 public n;
    function _bump() private returns (uint256) { n += 1; return n; }
    function _run() private returns (bool ok, bytes memory out) {
        (ok, out) = ITarget(target).run(_bump());
    }
    function run() external returns (bool ok, bytes memory out) {
        return _run();
    }
}
""",
        'run()',
        'FunctionCall: [solidity-import:unsupported] effectful arguments in typed external (scalar, bytes memory) call are outside this slice',
    ),
    # Rejection: value-bearing {value: 1} call options on external tuple call
    (
        'reject-value-call-options',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 a) external payable returns (bool, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 a) private returns (bool ok, bytes memory out) {
        (ok, out) = ITarget(target).run{value: 1}(a);
    }
    function run(uint256 a) external payable returns (bool ok, bytes memory out) {
        return _run(a);
    }
}
""",
        'run(uint256)',
        'Assignment: [solidity-import:unsupported] forwarded bytes result requires assignment from abi.encode or abi.encodePacked',
    ),
    # Rejection: fixed-size enum array as first return component (96-byte head, not 64-byte)
    (
        'reject-enum-fixed-array-first-component',
        """pragma solidity 0.8.34;
enum Operation { Call, DelegateCall }
interface ITarget {
    function run(uint256 x) external returns (Operation[2] memory, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (, out) = ITarget(target).run(x);
        ok = true;
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] typed external (scalar, bytes memory) call scalar return must be uint256, uint8..uint248, int256, bytes32, bytes4, bytes1, bool, address or enum',
    ),
    # Rejection: dynamic enum array as first return component
    (
        'reject-enum-dyn-array-first-component',
        """pragma solidity 0.8.34;
enum Operation { Call, DelegateCall }
interface ITarget {
    function run(uint256 x) external returns (Operation[] memory, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (, out) = ITarget(target).run(x);
        ok = true;
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] typed external (scalar, bytes memory) call scalar return must be uint256, uint8..uint248, int256, bytes32, bytes4, bytes1, bool, address or enum',
    ),
    # Rejection: dynamic contract/interface array as first return component
    (
        'reject-contract-array-first-component',
        """pragma solidity 0.8.34;
interface IFoo {}
interface ITarget {
    function run(uint256 x) external returns (IFoo[] memory, bytes memory);
}
contract C {
    address public target;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (, out) = ITarget(target).run(x);
        ok = true;
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] typed external (scalar, bytes memory) call scalar return must be uint256, uint8..uint248, int256, bytes32, bytes4, bytes1, bool, address or enum',
    ),
    # Rejection: unmodelled post-call extcodehash after closed CALL
    (
        'reject-post-call-codehash',
        """pragma solidity 0.8.34;
interface ITarget {
    function run(uint256 x) external returns (bool, bytes memory);
}
contract C {
    address public target;
    bytes32 public lastHash;
    function _run(uint256 x) private returns (bool ok, bytes memory out) {
        (ok, out) = ITarget(target).run(x);
        lastHash = target.codehash;
    }
    function run(uint256 x) external returns (bool ok, bytes memory out) {
        return _run(x);
    }
}
""",
        'run(uint256)',
        'MemberAccess: [solidity-import:unsupported] code hash read after an external call or create2 is unsupported',
    ),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--case', action='append', default=[])
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    if args.output:
        output = args.output.resolve()
        output.mkdir(parents=True, exist_ok=True)
    else:
        output = Path(tempfile.mkdtemp(prefix='forwarded-bytes-tuple-rej-', dir=root / '.lake')).resolve()

    selected = [c for c in CASES if not args.case or c[0] in args.case]
    if not selected:
        raise SystemExit(f'no matching cases for {args.case}')

    for name, src, fn_sig, expected in selected:
        case_dir = output / name
        case_dir.mkdir(parents=True, exist_ok=True)
        (case_dir / 'Fixture.sol').write_text('// SPDX-License-Identifier: MIT\n' + src)
        rel = case_dir.relative_to(root)
        lean_file = case_dir / 'Check.lean'
        lean_file.write_text(
            'import Compiler.SolidityImport.Import\n'
            f'solidity_import imported from "{rel}" entry "Fixture.sol"\n'
            '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
            '  contract C\n'
            f'  function {fn_sig}\n'
        )
        res = subprocess.run(
            ['lake', 'env', 'lean', str(lean_file)],
            cwd=root,
            text=True,
            capture_output=True,
            timeout=900,
        )
        combined = res.stdout + res.stderr
        if expected is None:
            if res.returncode != 0:
                raise SystemExit(f'[{name}] expected positive control to succeed, got:\n{combined}')
            print(f'PASS positive: {name}')
        else:
            if res.returncode == 0:
                raise SystemExit(f'[{name}] expected rejection containing {expected!r}, but succeeded!')
            if expected not in combined:
                raise SystemExit(f'[{name}] expected {expected!r}, got:\n{combined}')
            print(f'PASS rejected: {name}')

    print(f'All {len(selected)}/{len(selected)} forwarded-bytes-tuple rejection/control cases passed.')


if __name__ == '__main__':
    main()
