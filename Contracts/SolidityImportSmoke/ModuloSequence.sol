// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        value = x % 10 + uint256(uint8(x) % uint8(7));
        emit Changed(value);
        return value;
    }
    function fail() external view {
        require(7 % (value - value) == 1, "unreachable");
    }
    function read() external view returns (uint256) { return value; }
}
