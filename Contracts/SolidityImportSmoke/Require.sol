// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract RequireFixture {
    function checked(uint256 value) external pure returns (uint256) {
        require(value > 7, unicode"échec");
        return value;
    }
}
