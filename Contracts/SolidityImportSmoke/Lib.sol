// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

library L {
    function min(uint256 x, uint256 y) internal pure returns (uint256 z) {
        assembly {
            z := xor(x, mul(xor(x, y), lt(y, x)))
        }
    }

    function mulDivDown(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y) / d;
    }

    function mulDivUp(uint256 x, uint256 y, uint256 d) internal pure returns (uint256) {
        return (x * y + (d - 1)) / d;
    }

    function unused() internal pure returns (uint256) {
        uint256 s = 0;
        for (uint256 i = 0; i < 3; i++) {
            s += i;
        }
        return s;
    }
}
