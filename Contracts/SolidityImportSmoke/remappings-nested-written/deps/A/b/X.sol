// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// forge build keeps a/ and drops the nested a/b/, so a/b/X.sol is this file.
library X {
    function firstValue() internal pure returns (uint256) {
        return 1;
    }
}
