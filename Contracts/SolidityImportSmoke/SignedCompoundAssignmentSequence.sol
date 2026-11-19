// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
// Compound assignment and increment/decrement on narrow signed integers: checked code
// reverts with Panic(0x11) when the result leaves the declared range, unchecked code wraps.
// A narrow signed local assigned in Yul can hold a dirty word; the compound assignment cleans it.
contract SequenceFixture {
    int256 private acc;
    int256 private wrapped;
    uint256 private count;
    function change(uint256 x) external returns (int24) {
        int24 d = int24(int256(x & 0xffffff) - 0x800000);
        int24 a = int24(acc);
        a += d;
        int24 w = int24(wrapped);
        unchecked {
            w += d;
            w -= int24(int256(x >> 248));
            w++;
        }
        int8 small = int8(int256((x >> 24) % 256) - 128);
        if (((x >> 32) & 1) == 1) {
            small--;
        } else {
            small += 1;
        }
        int24 dirty = 0;
        assembly {
            dirty := shr(64, x)
        }
        dirty += 1;
        if (((x >> 40) & 1) == 1) {
            a++;
        }
        acc = a;
        wrapped = w;
        count += uint256(int256(small) + 128) + uint256(int256(dirty) + 0x800001);
        return a;
    }
    function fail() external {
        int24 a = int24(int256(0x7fffff));
        a++;
        acc = a;
    }
    function read() external view returns (int256, int256, uint256) {
        return (acc, wrapped, count);
    }
}
