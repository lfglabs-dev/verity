// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;
import {UtilsLib} from "src/libraries/UtilsLib.sol";
contract MulDivDown {
    function mulDivDown(uint256 x, uint256 y, uint256 d) external pure returns (uint256) {
        return UtilsLib.mulDivDown(x, y, d);
    }
}
