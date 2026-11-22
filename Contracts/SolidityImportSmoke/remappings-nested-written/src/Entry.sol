// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {X} from "a/b/X.sol";

/// Two nested written remappings.
contract Entry {
    function value() external pure returns (uint256) {
        return X.firstValue();
    }
}
