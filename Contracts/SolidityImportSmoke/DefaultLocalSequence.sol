// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        uint256 initial;
        uint8 small;
        address previousCollateralToken;
        bool enabled;
        bytes32 digest;
        require(initial == 0 && small == 0, "integer default");
        require(previousCollateralToken == address(0), "address default");
        require(!enabled && digest == bytes32(0), "scalar default");
        value = x + initial + uint256(small);
        emit Changed(value);
        return value;
    }
    function fail() external view {
        address previousCollateralToken;
        require(previousCollateralToken != address(0), "zero address");
    }
    function read() external view returns (uint256) { return value; }
}
