// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

uint256 constant WAD = 1e18;
uint256 constant DAY = 1 days;
uint256 constant DOUBLE_DAY = 2 * DAY;

contract SequenceFixture {
    uint256 private value;
    event Changed(uint256 value);

    function shadow(uint256 WAD) internal pure returns (uint256) {
        return WAD;
    }

    function duration(uint256 x) internal pure returns (uint256) {
        return shadow(x) + DOUBLE_DAY + 1 seconds + 2 minutes + 3 hours + 4 days + 5 weeks
            + 0.5 hours + .5 hours + 1.25 days;
    }

    function change(uint256 x) external returns (uint256) {
        value = duration(x) + WAD + 7 wei + 8 gwei + 9 ether
            + 0.01e18 + 0.000014e18 + 1e-3 ether + 2E3 + 0x20 + (1_000 + 0x2_0);
        emit Changed(value);
        return value;
    }

    function fail() external {
        require(value == 1 weeks, "week");
    }

    function read() external view returns (uint256) {
        return value;
    }
}
