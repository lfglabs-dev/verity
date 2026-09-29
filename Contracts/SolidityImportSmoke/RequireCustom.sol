// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract RequireCustomFixture {
    error BadValue(uint256 value, address account, bool enabled, bytes32 tag, uint8 small, uint16 medium, uint128 wide);
    function checked(uint256 value, address account, bool enabled, bytes32 tag, uint8 small, uint16 medium, uint128 wide) external pure returns (uint256) {
        require(value > 7, BadValue(value, account, enabled, tag, small, medium, wide));
        return value;
    }
}
