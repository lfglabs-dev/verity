// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);
    function change(uint256 x) external returns (uint256) {
        require(x <= 8, "bound");
        uint256 total;
        uint256 bound = x;
        for (uint256 i = 0; i < bound; i++) {
            total = total + i + 1;
            value = total;
            emit Changed(value);
            if (i == 7) return value;
        }
        value = total;
        return value;
    }
    function fail() external view {
        require(value <= 36, "range");
        for (uint256 j = 0; j < 2; j++) {
            require(j == 0, "loop revert");
        }
    }
    function read() external view returns (uint256) { return value; }
}
