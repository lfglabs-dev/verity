// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "./yul/YulTestBase.sol";

/**
 * @title PropertyRevertReturndataSmokeTest
 * @notice Auto-generated baseline property stubs from `verity_contract` declarations.
 * @dev Source: Contracts/Smoke/RevertReturndataSmoke.lean
 */
contract PropertyRevertReturndataSmokeTest is YulTestBase {
    address target;
    address alice = address(0x1111);

    function setUp() public {
        target = deployYul("RevertReturndataSmoke");
        require(target != address(0), "Deploy failed");
    }

    // Property 1: bubbleIf has no unexpected revert
    function testAuto_BubbleIf_NoUnexpectedRevert() public {
        vm.prank(alice);
        (bool ok,) = target.call(abi.encodeWithSignature("bubbleIf(bool)", true));
        require(ok, "bubbleIf reverted unexpectedly");
    }
}
