// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {DepMath} from "dep/DepMath.sol";
import {Local} from "./Local.sol";

/// Resolved by a written remapping ending in `/` and a relative import under `src/`: only
/// library configurations are read.
contract Entry {
    function value() external pure returns (uint256) {
        return DepMath.depValue() + Local.localValue();
    }
}
