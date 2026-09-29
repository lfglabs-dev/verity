// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private stored;
    error BadValue(uint256 previous);
    function change(uint256 value) external returns (uint256) {
        uint256 old = stored;
        require(value != 0, BadValue(old));
        stored = value;
        return old;
    }
    function fail() external {
        stored = 99;
        require(false, unicode"échec");
    }
    function read() external view returns (uint256) { return stored; }
}
