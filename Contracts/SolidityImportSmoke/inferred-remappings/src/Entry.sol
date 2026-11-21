// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {DepMath} from "dep/DepMath.sol";
import {Scale} from "local/Scale.sol";

/// Imports one library through an inferred remapping (`dep/` from `deps/dep/src/`) and one
/// through a written remapping.
contract Entry {
    function combined(uint256 x) external pure returns (uint256) {
        return Scale.plusOne(DepMath.twice(x));
    }
}
