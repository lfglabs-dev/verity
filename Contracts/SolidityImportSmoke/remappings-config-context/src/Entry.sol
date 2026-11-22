// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {A} from "@oz/A.sol";

/// The import of A from src/ takes the library's context remapping in forge build.
contract Entry {
    function value() external pure returns (uint256) {
        return A.ozValue();
    }
}
