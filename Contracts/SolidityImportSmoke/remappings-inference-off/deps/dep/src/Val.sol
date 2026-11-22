// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// Foundry would infer dep/ to here if auto-detection were on.
library Val {
    function depValue() internal pure returns (uint256) {
        return 2;
    }
}
