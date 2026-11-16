// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyFallbackReentrancyTrustedSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Declarations.lean
 */
contract PropertyFallbackReentrancyTrustedSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("FallbackReentrancyTrustedSmoke");
        require(target != address(0), "Deploy failed");
    }

}
