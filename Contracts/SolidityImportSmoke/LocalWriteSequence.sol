// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        uint256 current;
        current = x;
        uint8 small = uint8(x);
        small = uint8(current);
        address previousCollateralToken;
        previousCollateralToken = address(uint160(current));
        bool enabled;
        enabled = current != 0;
        bytes32 digest;
        digest = bytes32(current);
        require(uint256(digest) == current, "bytes local");
        require(previousCollateralToken == address(uint160(x)), "address local");
        require(enabled == (x != 0), "bool local");
        { uint256 current = 7; current = 8; require(current == 8, "shadow"); }
        require(current == x, "outer");
        delete current;
        value = uint256(small) + current;
        emit Changed(value);
        return value;
    }
    function fail() external view {
        uint256 local;
        local = value;
        require(local != value, "local revert");
    }
    function read() external view returns (uint256) { return value; }
}
