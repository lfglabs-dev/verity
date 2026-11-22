// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

/// An unrelated library the importer never needs to scan.
library Other {
    function otherValue() internal pure returns (uint256) {
        return 9;
    }
}
