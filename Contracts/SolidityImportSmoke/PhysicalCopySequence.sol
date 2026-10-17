// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract SequenceFixture {
    uint256 private observed;

    function change(uint256 value) external returns (uint256 result) {
        assembly {
            mstore(0, value)
            calldatacopy(3, 4, 17)
            // A later physical write must preserve the bytes just copied.
            mstore(128, 99)
            result := mload(0)
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
