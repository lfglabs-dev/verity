// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private saved;

    function change(uint256 next) external returns (uint256) {
        saved = next;
        if (next % 2 != 0) revert();
        return saved;
    }

    function fail() external {
        saved = 99;
        revert();
    }

    function read() external view returns (uint256) {
        return saved;
    }
}
