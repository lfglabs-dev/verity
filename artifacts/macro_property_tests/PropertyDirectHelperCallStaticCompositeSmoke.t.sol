// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallStaticCompositeSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallStaticCompositeSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallStaticCompositeSmoke");
        require(target != address(0), "Deploy failed");
    }

}
