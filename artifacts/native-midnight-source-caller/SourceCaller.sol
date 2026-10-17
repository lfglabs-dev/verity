// SPDX-License-Identifier: GPL-2.0-or-later
pragma solidity ^0.8.0;
import {IdLib} from "src/libraries/IdLib.sol";
import {Market} from "src/interfaces/IMidnight.sol";
contract SourceCaller {
    mapping(uint256 => uint256) public values;
    function deploy(Market memory market, uint256 key, uint256 value) external returns (address) {
        values[key] = value;
        return IdLib.storeInCode(market);
    }
}
