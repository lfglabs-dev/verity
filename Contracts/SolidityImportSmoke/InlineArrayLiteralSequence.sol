// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    uint256 private last;
    function field(uint256[4] memory t, uint256 k) internal pure returns (uint256) {
        return (t[k >> 1] >> (32 * (k & 1))) & 0xffffffff;
    }
    function change(uint256 x) external returns (uint256) {
        uint256[4] memory table = [uint256(0x0000000100000002), 0x0000000300000004, 0x0000000500000006, 0x0000000700000008];
        uint256 acc = 0;
        for (uint256 k = 0; k < 8; k++) {
            acc = acc * 3 + field(table, k);
        }
        uint256[3] memory mixed = [x & 0xffff, x >> 240, uint256(7)];
        mixed[x % 3] += 1;
        uint8[3] memory small = [1, 2, 3];
        table = [uint256(9), 8, 7, x % 5];
        value = acc + mixed[0] * 5 + mixed[1] * 7 + mixed[2] * 11 + uint256(small[x % 3]) * 13 + table[x % 4];
        last = field([uint256(0x0000000a0000000b), 0x0000000c0000000d, 0, 0], x % 9);
        return value;
    }
    function fail() external {
        uint256[2] memory probe = [value, value + 1];
        value = probe[value % 2 + 2];
    }
    function read() external view returns (uint256, uint256) {
        return (value, last);
    }
}
