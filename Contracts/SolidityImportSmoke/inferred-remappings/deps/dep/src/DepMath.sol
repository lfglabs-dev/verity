// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Bounds} from "./Bounds.sol";

/// A library under a Foundry `libs` directory, reached only through an inferred remapping.
library DepMath {
    function twice(uint256 x) internal pure returns (uint256) {
        require(x <= Bounds.MAX_INPUT, "too large");
        return x + x;
    }
}
