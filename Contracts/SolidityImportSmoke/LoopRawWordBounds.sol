// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Loop shapes whose trip count or observed counter depends on raw narrow stack words
// (written by inline assembly): a sign-widened bound for a pre-declared counter, a
// narrow decrementing helper loop with `continue` whose counter is read in Yul, and a
// tail-window helper loop with `break` over a narrow bound.
contract LoopRawWordBounds {
    uint256 private a;
    uint256 private b;

    function signedWidenedBound(uint256 x) external pure returns (uint256) {
        int8 v = 0;
        assembly { v := x }
        int256 w = v;
        uint256 n = uint256(w);
        uint256 i;
        for (i = 0; i < n; ++i) {}
        return i;
    }

    function _narrowDecrement(uint256 raw) internal pure returns (uint256 observed) {
        uint8 start;
        assembly { start := raw }
        for (uint8 d = start; d > 0; d--) {
            assembly { observed := d }
            if (d == 1) continue;
        }
    }

    function narrowDecrementRawRead(uint256 x) external pure returns (uint256) {
        return _narrowDecrement(x);
    }

    function _tailWindow(uint256 raw) internal view returns (uint256) {
        uint8 n;
        assembly { n := raw }
        for (uint256 i = n - 1; i < n; i++) {
            if (i != a + b) {
                break;
            }
            return 10;
        }
        return 20;
    }

    function tailWindowNarrowBreak(uint256 x) external view returns (uint256) {
        return _tailWindow(x);
    }
}
