// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Val} from "dep/Val.sol";

/// With auto_detect_remappings = false, dep/Val.sol is the project file.
contract Entry {
    function value() external pure returns (uint256) {
        return Val.projectValue();
    }
}
