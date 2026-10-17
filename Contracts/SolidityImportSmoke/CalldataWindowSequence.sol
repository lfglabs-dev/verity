// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private observed;

    function change(uint256 value) external returns (uint256 result) {
        assembly {
            // Exercise each 32-byte window crossing the four-byte selector.
            result := calldataload(mod(value, 4))
        }
        observed = result;
    }

    function fail() external {
        observed = 99;
        assert(false);
    }

    function read() external view returns (uint256) {
        return observed;
    }
}
