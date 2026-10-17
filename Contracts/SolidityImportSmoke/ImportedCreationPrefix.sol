// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
import {Market} from "./pinned-midnight/IMidnight.sol";
contract SourcePrefix {
    mapping(uint256 => uint256) public values;
    bytes constant PREFIX = hex"600b380380600b5f395ff3";
    function deploy(Market memory market, uint256 key, uint256 value) external returns (bytes memory) {
        values[key] = value;
        return abi.encodePacked(PREFIX, abi.encode(market));
    }
}
