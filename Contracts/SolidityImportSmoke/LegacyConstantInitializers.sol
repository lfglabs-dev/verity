// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library LegacyConstantInitializers {
    uint256 internal constant QUOTIENT = uint256(10) / (uint256(1) << 256);
    uint256 internal constant ALIAS = QUOTIENT;
    uint256 internal constant IN_RANGE = uint8(42);
}
