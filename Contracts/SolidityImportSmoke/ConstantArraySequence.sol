// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
uint256 constant FIRST = 1;
uint256 constant LAST = 8;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        value = [FIRST, 2, 3, 4, 5, 6, 7, LAST][x - (x / 8) * 8];
        emit Changed(value);
        return value;
    }
    function fail() external view {
        require([FIRST, 2, 3, 4, 5, 6, 7, LAST][value] == FIRST, "first");
    }
    // Exercise every table entry, independently of random sequence coverage.
    function entry(uint256 index) internal pure returns (uint256) {
        return [FIRST, 2, 3, 4, 5, 6, 7, LAST][index];
    }
    function read() external view returns (uint256) {
        return value + entry(0) + entry(1) + entry(2) + entry(3)
            + entry(4) + entry(5) + entry(6) + entry(7);
    }
}
