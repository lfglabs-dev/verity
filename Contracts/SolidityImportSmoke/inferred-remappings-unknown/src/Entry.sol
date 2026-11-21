// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;

import {DepMath} from "dep/DepMath.sol";

/// Needs the inferred `dep/` remapping while `deps/bad/foundry.toml` cannot be checked.
contract Entry {
    function twice(uint256 x) external pure returns (uint256) {
        return DepMath.twice(x);
    }
}
