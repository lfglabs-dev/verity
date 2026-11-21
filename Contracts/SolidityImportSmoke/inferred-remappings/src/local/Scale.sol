// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// Reached through the explicit `local/` remapping.
library Scale {
    function plusOne(uint256 x) internal pure returns (uint256) {
        return x + 1;
    }
}
