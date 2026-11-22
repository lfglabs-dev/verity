// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import {Shared} from "src/sub/Shared.sol";

/// deps/dep remaps src/sub/ to its own src/.
contract Entry {
    function value() external pure returns (uint256) {
        return Shared.depValue();
    }
}
