// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyGenericECMTripleResultSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/ExternalCalls.lean
 */
contract PropertyGenericECMTripleResultSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("GenericECMTripleResultSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: storeThird has no unexpected revert
    function testAuto_StoreThird_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("storeThird()"));
        require(ok, "storeThird reverted unexpectedly");
    }
}
