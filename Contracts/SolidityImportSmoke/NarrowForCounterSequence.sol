// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private total;
    uint256 private runs;

    function _sum8(uint256 n) internal pure returns (uint256 acc) {
        for (uint8 i = 0; i < n; i++) {
            acc += uint256(i) * 3 + 1;
        }
    }

    function change(uint256 x) external returns (uint256) {
        uint16 m = uint16(x % 1000);
        uint128 half = uint128(x % 40);
        uint256 acc;
        for (uint16 i = 0; i < m; ++i) {
            acc += i;
        }
        for (uint128 j = 0; j < half; j++) {
            acc += uint256(j) * 2;
        }
        for (uint8 t = 0; t < 10; t++) {
            acc += t;
        }
        uint32 start = uint32(x % 20);
        for (uint32 k = start; k > 0; k--) {
            acc += k;
        }
        // A literal bound of 2^8: solc compares in uint16, so `u` reaches 255 and
        // the checked `u++` panics.
        if (x == 999) {
            for (uint8 u = 0; u < 256; u++) {
                acc += 1;
            }
        }
        // A uint16 bound wider than the uint8 counter: w = 255 completes, w = 256
        // panics after the v = 255 iteration.
        if (x >= 255000 && x < 257000) {
            uint16 w = uint16(x / 1000);
            for (uint8 v = 0; v < w; v++) {
                acc += v;
            }
        }
        acc += _sum8(x % 300);
        total += acc;
        runs += 1;
        return total;
    }

    function fail() external {
        total += _sum8(256);
    }

    function read() external view returns (uint256, uint256) {
        return (total, runs);
    }
}
