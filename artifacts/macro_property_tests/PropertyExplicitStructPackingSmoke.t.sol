// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyExplicitStructPackingSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/Storage.lean
 */
contract PropertyExplicitStructPackingSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("ExplicitStructPackingSmoke");
        require(target != address(0), "Deploy failed");
    }

}
