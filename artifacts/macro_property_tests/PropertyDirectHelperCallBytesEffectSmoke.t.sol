// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyDirectHelperCallBytesEffectSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/HelperCalls.lean
 */
contract PropertyDirectHelperCallBytesEffectSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("DirectHelperCallBytesEffectSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: consumePayload has no unexpected revert
    function testAuto_ConsumePayload_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("consumePayload(bytes)", hex"CAFE"));
        require(ok, "consumePayload reverted unexpectedly");
    }
    // Property 2: run has no unexpected revert
    function testAuto_Run_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("run(bytes)", hex"CAFE"));
        require(ok, "run reverted unexpectedly");
    }
}
