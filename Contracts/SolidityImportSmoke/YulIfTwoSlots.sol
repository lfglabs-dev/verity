// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// An inline-assembly `if` runs its body exactly when its condition is a nonzero word,
// whatever else the contract declares (#2830). The importer counts state variables across
// the whole compiled source, so each contract of the pair is alone in its file; they differ
// only by one unrelated state variable and one unused function.
contract YulIfTwoSlots {
    uint256 internal stored;
    uint256 internal unrelated;

    function unused() external { unrelated = 1; }

    function clamp(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            r := x
            if gt(x, 10) { r := 10 }
        }
    }

    function guarded(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            if gt(x, 100) { revert(0, 0) }
            r := add(x, 1)
        }
    }

    function selectorRevert(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            if eq(x, 7) {
                mstore(0, 0xdeadbeef)
                revert(0x1c, 4)
            }
            r := x
        }
    }

    function nested(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            if x {
                let y := add(x, 1)
                if gt(y, 5) { r := y }
            }
        }
    }

    function boolCondition(uint256 x) external returns (uint256 r) {
        stored = x;
        assembly {
            r := x
            if true { r := add(r, 2) }
            if false { r := 0 }
        }
    }
}
