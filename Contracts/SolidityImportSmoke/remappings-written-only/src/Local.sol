// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// Reached by a relative import.
library Local {
    function localValue() internal pure returns (uint256) {
        return 1;
    }
}
