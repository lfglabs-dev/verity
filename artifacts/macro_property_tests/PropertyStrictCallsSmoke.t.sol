// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyStrictCallsSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/StrictCallsSmoke.lean
 */
contract PropertyStrictCallsSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("StrictCallsSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: failHop has no unexpected revert
    function testAuto_FailHop_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("failHop()"));
        require(ok, "failHop reverted unexpectedly");
    }
}
