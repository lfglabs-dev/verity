// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyVoidViewInterfaceCallSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/InternalInterfaceSmoke.lean
 */
contract PropertyVoidViewInterfaceCallSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("VoidViewInterfaceCallSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: pingHook has no unexpected revert
    function testAuto_PingHook_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("pingHook(address,address)", alice, alice));
        require(ok, "pingHook reverted unexpectedly");
    }
}
