// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyTryCatchSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/TryCatch.lean
 */
contract PropertyTryCatchSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("TryCatchSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: failHop has no unexpected revert
    function testAuto_FailHop_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("failHop()"));
        require(ok, "failHop reverted unexpectedly");
    }
    // Property 2: okHop has no unexpected revert
    function testAuto_OkHop_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("okHop()"));
        require(ok, "okHop reverted unexpectedly");
    }
}
