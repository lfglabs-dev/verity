// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Custom errors with signed parameters: each argument is ABI-encoded as a sign-extended
// word and the selector hashes `intN`. `toInt104` has the shape of a checked downcast
// helper that reports the original `int256`. Each revert follows a storage write, which
// the revert rolls back.
contract SequenceFixture {
    error IntDowncastOverflow(uint8 bits, int256 value);
    error Narrow(int8 low, int104 mid, int24 odd);
    error Bounds(int256 lo, int64 hi);

    uint256 private saved;

    function toInt104(int256 value) internal pure returns (int104 downcasted) {
        downcasted = int104(value);
        if (downcasted != value) {
            revert IntDowncastOverflow(104, value);
        }
    }

    function change(uint256 next) external returns (uint256) {
        saved = next;
        int256 wide = int256(next);
        if (next % 4 == 1) {
            int104 cast = toInt104(wide);
            saved = uint256(int256(cast));
            return saved;
        }
        int8 low = int8(wide);
        int104 mid = int104(wide >> 8);
        int24 odd = int24(wide >> 112);
        if (next % 4 == 2) {
            revert Narrow(low, mid, odd);
        }
        if (next % 4 == 3) {
            revert Bounds(type(int256).min, -1);
        }
        return saved;
    }

    function fail() external {
        saved = 99;
        revert Narrow(type(int8).min, type(int104).max, -8388608);
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
